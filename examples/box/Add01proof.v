Require Import Mem0 Mem1 SimModSem Hoare.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import Add0 Add1 BoxHeader.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.









Definition tauK {E R}: R -> itree E R := fun r => tau;; Ret r.




Lemma interp_vis:
  forall (E F : Type -> Type) (R : Type) (f : forall T : Type, E T -> itree F T) (U : Type) (e : E U) (k : U -> itree E R),
  interp f (Vis e k) = ` x : U <- f U e;; (tau;; interp f (k x))
.
Proof. i. f. eapply interp_vis. Qed.

Lemma interp_ret: forall (E F : Type -> Type) (R : Type) (f : forall T : Type, E T -> itree F T) (x : R),
    interp f (Ret x) = Ret x.
Proof. i. f. eapply interp_ret. Qed.

Lemma interp_tau: forall (E F : Type -> Type) (R : Type) (f : forall T : Type, E T -> itree F T) (t : itree E R),
  interp f (tau;; t) = (tau;; interp f t).
Proof. i. f. eapply interp_tau. Qed.

Lemma interp_trigger:
  forall (E F : Type -> Type) (R : Type) (f : forall T : Type, E T -> itree F T) (e : E R),
  interp f (ITree.trigger e) = x <- (f R e);; tau;; Ret x
  (* (f R e) >>= tauK *)
.
Proof.
  i. unfold ITree.trigger.
  rewrite interp_vis. f_equiv. apply func_ext. i. unfold tauK. repeat f_equiv. rewrite interp_ret. ss.
Qed.

Hint Unfold tauK.

Lemma interp_bind :
forall {E F : Type -> Type} {R S : Type} (f : forall T : Type, E T -> itree F T) 
  (t : itree E R) (k : R -> itree E S),
interp f (` x : _ <- t;; k x) = ` r : R <- interp f t;; interp f (k r).
Proof. i. f. apply interp_bind. Qed.



(*** black + delta --> new_black ***)
Definition add_delta_to_black `{M: URA.t} (b: URA.auth_t) (w: URA.auth_t): URA.auth_t :=
  match b, w with
  | URA.excl e _, URA.frag f1 => URA.excl (URA.add e f1) URA.unit
  | _, _ => URA.boom
  end
.







Ltac go := try first[pfold; econs; [..|M]; (Mskip ss); et; check_safe; ii; left|
                     pfold; econsr; [..|M]; (Mskip ss); et; check_safe; ii; left].
Ltac force_l := pfold; econs; [..|M]; Mskip ss; et.
Ltac force_r := pfold; econsr; [..|M]; Mskip ss; et.
Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG boxRA Σ}.

































  Lemma interp_state_bind:
  forall (E F : Type -> Type) (A B S : Type) (f : forall T : Type, E T -> S -> itree F (S * T)) (t : itree E A)
    (k : A -> itree E B) (s : S),
  interp_state f (` x : _ <- t;; k x) s = ` st : S * A <- interp_state f t s;; interp_state f (k (snd st)) (fst st)
  .
  Proof. i. f. apply interp_state_bind. Qed.

  Lemma interp_state_vis:
  forall (E F : Type -> Type) (S T U : Type) (e : E T) (k : T -> itree E U) (h : forall T0 : Type, E T0 -> stateT S (itree F) T0)
    (s : S), interp_state h (Vis e k) s = ` sx : S * T <- h T e s;; (tau;; interp_state h (k (snd sx)) (fst sx))
  .
  Proof.
    i. f. apply interp_state_vis.
  Qed.

  Lemma interp_state_tau :
    forall (E F : Type -> Type) (S T : Type) (t : itree E T) (h : forall T0 : Type, E T0 -> stateT S (itree F) T0) (s : S),
      interp_state h (tau;; t) s = (tau;; interp_state h t s)
  .
  Proof.
    i. f. apply interp_state_tau.
  Qed.

  Lemma interp_state_ret:
  forall (E F : Type -> Type) (R S : Type) (f : forall T : Type, E T -> S -> itree F (S * T)) (s : S) (r : R),
  interp_state f (Ret r) s = Ret (s, r)
  .
  Proof.
    i. f. apply interp_state_ret.
  Qed.

  Lemma unfold_interp:
    forall (E F : Type -> Type) (R : Type) (f : forall T : Type, E T -> itree F T) (t : itree E R),
      interp f t = _interp f (observe t)
  .
  Proof.
    i. f. apply unfold_interp.
  Qed.

  Definition my_interp A (prog: callE ~> itree Es) (itr0: itree Es A) (st0: ModSem.r_state) :=
    ModSem.interp_rE (interp_mrec prog itr0) st0
  .

  Ltac grind := repeat (f_equiv; try apply func_ext; ii; try (des_ifs; check_safe)).

  Lemma my_interp_bind
        (prog: callE ~> itree Es)
        A B
        (itr: itree Es A) (ktr: A -> itree Es B)
        st0
    :
      my_interp prog (v <- itr ;; ktr v) st0 =
      '(st1, v) <- my_interp prog (itr) st0 ;; my_interp prog (ktr v) st1
  .
  Proof.
    unfold my_interp.
    unfold ModSem.interp_rE.
    rewrite interp_mrec_bind.
    rewrite interp_state_bind.
    grind.
  Qed.

  Lemma my_interp_tau
        (prog: callE ~> itree Es)
        A
        (itr: itree Es A)
        st0
    :
      my_interp prog (tau;; itr) st0 = tau;; my_interp prog itr st0
  .
  Proof.
    unfold my_interp.
    unfold ModSem.interp_rE.
    rewrite unfold_interp_mrec. ss.
    rewrite interp_state_tau.
    grind.
  Qed.

  Lemma my_interp_ret
        T
        prog st0 (v: T)
    :
      my_interp prog (Ret v) st0 = Ret (st0, v)
  .
  Proof.
    unfold my_interp. unfold ModSem.interp_rE.
    rewrite unfold_interp_mrec. ss.
    rewrite interp_state_ret. ss.
  Qed.

  Lemma interp_mrec_hit:
    forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) (U : Type) (a : D U),
      interp_mrec ctx (trigger a) = (tau;; interp_mrec ctx (ctx _ a))
  .
  Proof.
    i. rewrite unfold_interp_mrec. ss.
    unfold resum, ReSum_id, id_, Id_IFun. rewrite bind_ret_r. ss.
  Qed.


  Definition idK {E R}: R -> itree E R := fun r => Ret r.
  Hint Unfold idK.

  Lemma idK_spec E R (i0: itree E R): i0 = i0 >>= idK. Proof. unfold idK. irw. refl. Qed.

  (*** TODO: I don't want "F" here, but it is technically needed. Report it to itree people? ***)
  Lemma interp_mrec_miss:
    (* forall (D E F: Type -> Type) `{F -< E} (ctx : forall T : Type, D T -> itree (D +' E) T) (U : Type) (a : F U), *)
    forall (D E F: Type -> Type) `{F -< E} (ctx : forall T : Type, D T -> itree (D +' E) T) (U : Type) (a : F U),
      interp_mrec ctx (trigger a) = x <- (trigger a);; tau;; Ret x
      (* (trigger a) >>= tauK *)
  .
  Proof.
    i. rewrite unfold_interp_mrec. cbn.
    unfold trigger. irw.
    grind. irw. ss.
  Qed.

  (*** TODO: interp_trigger_eqit does not exist. report to itree people? ***)
  Lemma interp_state_trigger:
  forall (E F : Type -> Type) (R S : Type) (e : E R) (f : forall T : Type, E T -> stateT S (itree F) T) (s : S),
  interp_state f (ITree.trigger e) s = ` x : S * R <- f R e s;; (tau;; Ret x)
  .
  Proof. i. f. apply interp_state_trigger_eqit. Qed.

  Lemma my_interp_callE
        p st0
        (* (e: Es Σ) *)
        (e: callE val)
    :
      my_interp p (trigger e) st0 = tau;; (my_interp p (p val e) st0)
  .
  Proof.
    unfold my_interp. unfold ModSem.interp_rE. rewrite interp_mrec_hit. cbn.
    rewrite interp_state_tau. grind.
  Qed.

  Lemma my_interp_rE
        p st0
        (* (e: Es Σ) *)
        T
        (e: rE T)
    :
      my_interp p (trigger e) st0 =
      '(st1, r) <- ModSem.handle_rE e st0;;
      tau;; tau;;
      Ret (st1, r)
      (* interp_state (case_ ModSem.handle_rE pure_state) (tau;; Ret r) st1 *)
  .
  Proof.
    unfold my_interp. unfold ModSem.interp_rE.
    (* rewrite unfold_interp_mrec. cbn. *)
    unfold Es.
    rewrite interp_mrec_miss with (D:=callE) (E:=rE +' eventE) (F:=rE) (a:=e).
    rewrite interp_state_bind.
    rewrite interp_state_trigger. irw. grind. irw. grind.
    rewrite interp_state_tau. grind.
    rewrite interp_state_ret. ss.
  Qed.

  Lemma my_interp_eventE
        p st0
        (* (e: Es Σ) *)
        T
        (e: eventE T)
    :
      my_interp p (trigger e) st0 = r <- trigger e;; tau;; tau;; Ret (st0, r)
  .
  Proof.
    unfold my_interp. unfold ModSem.interp_rE.
    (* rewrite unfold_interp_mrec. cbn. *)
    unfold Es.
    rewrite interp_mrec_miss with (D:=callE) (E:=rE +' eventE) (F:=eventE) (a:=e).
    rewrite interp_state_bind.
    rewrite interp_state_trigger. irw. unfold pure_state.
    unfold resum, ReSum_id, id_, Id_IFun.
    irw. grind. irw. grind.
    rewrite interp_state_tau. grind.
    rewrite interp_state_ret. ss.
  Qed.

  Lemma my_interp_triggerUB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (my_interp prog (triggerUB) st0: itree eventE (_ * A)) = triggerUB
  .
  Proof.
    unfold triggerUB. rewrite my_interp_bind. rewrite my_interp_eventE.
    irw. grind.
  Qed.

  Lemma my_interp_triggerNB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (my_interp prog (triggerNB) st0: itree eventE (_ * A)) = triggerNB
  .
  Proof.
    unfold triggerNB. rewrite my_interp_bind. rewrite my_interp_eventE.
    irw. grind.
  Qed.

  Ltac igo := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r; try rewrite bind_tau;
                      try rewrite interp_vis;
                      try rewrite interp_ret;
                      try rewrite interp_tau;
                      (* try rewrite interp_trigger *)
                      try rewrite interp_bind
                     ).



















  Let W: Type := (alist mname Σ) * (alist mname Σ).

  Let wf: W -> Prop :=
    fun '(mrs_src0, mrs_tgt0) =>
      exists mr_src mr_tgt,
        (<<SRC: alist_find Dec_RelDec "Add" mrs_src0 = Some mr_src>>) /\
        (<<TGT: alist_find Dec_RelDec "Add" mrs_tgt0 = Some mr_tgt>>)
  .

  Local Opaque GRA.to_URA.
  Infix "⋅" := URA.add (at level 50, left associativity).
  Notation "(⋅)" := URA.add (only parsing).

  Local Opaque AddStb BoxStb.
  Local Opaque string_dec.
  Theorem correct: ModSemPair.sim Add1.AddSem Add0.AddSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. esplits; ss; et. }
    econs; ss.
    { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify.
      unfold alist_add, alist_remove; ss.
      unfold addF.
      repeat (go; igo; ss).
      unfold assume, guarantee.
      repeat (go; igo; ss).
      des; clarify.
      rewrite ! URA.unit_idl.
      (* unfold unwrapU. des_ifs. igo. *)
      unfold addBody.
      unfold body_to_tgt. unfold interp_hCallE_tgt. igo. rewrite interp_trigger. cbn. des_ifs.
      Local Transparent BoxStb AddStb.
      cbn in Heq.
      Local Opaque BoxStb AddStb.
      des_ifs. cbn in *. clear_tac.
      repeat (go; igo; ss).
      rewrite URA.unit_idl in WF.
      unfold HoareCall.
      repeat (go; igo; ss).


      force_l. eexists (mr_src, client x). left.
      repeat (go; igo; ss).
      force_l. left.
      force_l. eexists. left.
      repeat (go; igo; ss).
      force_l. { rewrite URA.unit_idl; try refl. } left.
      force_l. eexists. left.
      repeat (go; igo; ss).
      unfold assume, guarantee.
      repeat (go; igo; ss).
      force_l. unshelve eexists; et. left.
      pfold; econs; et.
      { ss. esplits; et. }
      ii. exists 100%nat. left.
      repeat (go; igo; ss). des.
      repeat (go; igo; ss). des. clarify.
      repeat (go; igo; ss).
      rewrite interp_trigger.
      repeat (go; igo; ss). cbn. des_ifs.
      Local Transparent BoxStb AddStb.
      cbn in Heq.
      Local Opaque BoxStb AddStb.
      des_ifs. cbn in *.
      unfold HoareCall.
      repeat (go; igo; ss).
      force_l. eexists (mr_src0, client x). left.
      repeat (go; igo; ss).
      force_l. { rewrite URA.unit_idl. eapply URA.updatable_add; try refl. } left.
      force_l. eexists (client x). left.
      repeat (go; igo; ss).
      force_l. { rewrite URA.unit_idl; ss. } left.
      force_l. exists ((x+1)%Z). left.
      repeat (go; igo; ss).
      unfold assume, guarantee.
      repeat (go; igo; ss).
      force_l. unshelve eexists; et. left.
      rewrite idK_spec with (i0:=trigger (Call "set" [Vint (x+1)])). unfold idK at 1. rewrite bind_bind.
      pfold. econs; ss; et.
      ii. des. eexists 100%nat. left.
      repeat (go; igo; ss). clarify.
      force_l. eexists (mr_src1, client (x+1)). left.
      force_l. { rewrite URA.unit_idl. eapply URA.updatable_add; try refl. } left.
      force_l. eexists (client (x+1)). left.
      repeat (go; igo; ss).
      force_l. unshelve eexists; et. left.
      force_l. { rewrite URA.unit_idl; ss. } left.
      pfold. econs; ss; et.
    }
  Qed.

End SIMMODSEM.


