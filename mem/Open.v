Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic.
(* Require Import Mem0 MemOpen. *)
Require Import HoareDef Hoare.
Require Import OpenDef.
Require Import IRed.

Set Implicit Arguments.






Global Program Instance Forall2_Reflexive `{Reflexive A R}: Reflexive (Forall2 R).
Next Obligation. induction x; ii; ss. econs; ss. Qed.

Global Program Instance Forall2_Transitive `{Transitive A R}: Transitive (Forall2 R).
Next Obligation.
  i. revert_until x. induction x; ii; ss.
  { inv H0. inv H1. ss. }
  inv H0. inv H1. econs; ss; et.
Qed.

Global Program Instance Forall2_PreOrder `{PreOrder A R}: PreOrder (Forall2 R).

Lemma flat_map_map A B C (f: A -> B) (g: B -> list C) (l: list A)
  :
    flat_map g (map f l) = flat_map (g ∘ f) l.
Proof.
  induction l; ss. f_equal; auto.
Qed.

Lemma alist_find_map_snd K R `{RD_K: @RelDec K R} A B (f: A -> B) (l: alist K A) k
  :
    alist_find k (map (map_snd f) l)
    =
    o_map (alist_find k l) f.
Proof.
  induction l; ss. destruct a. ss. uo. des_ifs.
Qed.

(*** TODO: move ***)
Definition trivial_state_Handler `{E -< F} {S}: E ~> (stateT S (itree F)) :=
  fun T X s => x <- trigger X;; Ret (s, x).



Module Massage.
Section MASSAGE.

  Context `{Σ: GRA.t}.

  (* Variant frE: Type -> Type := *)
  (* | FPut' (fr0: Σ): frE unit *)
  (* | FGet': frE Σ *)
  (* . *)
  Definition massage_callE: callE ~> stateT Σ (itree Es') :=
    fun T '(Call fn args) fr0 => r <- trigger (hCall false fn args);; Ret (fr0, r)
  .

  Definition massage_rE: rE ~> stateT Σ (itree Es') :=
    fun T re fr0 =>
      match re with
      | FPut fr1 => Ret (fr1, tt)
      | FGet => Ret (fr0, fr0)
      | MPut mr0 =>
        stmr0 <- trigger (PGet);;
        '(st0, _) <- (Any.split stmr0)ǃ;;
        trigger (PPut (Any.pair st0 mr0↑));;;
        Ret (fr0, tt)
      | MGet =>
        stmr0 <- trigger (PGet);;
        '(_, mr0) <- (Any.split stmr0)ǃ;;
        `mr0: Σ <- mr0↓ǃ;;
        Ret (fr0, mr0)
      end
  .

  Definition massage_pE: pE ~> stateT Σ (itree Es') :=
    fun T pe fr0 =>
      match pe with
      | PPut st0 =>
        stmr0 <- trigger (PGet);;
        '(_, mr0) <- (Any.split stmr0)ǃ;;
        trigger (PPut (Any.pair st0 mr0));;;
        Ret (fr0, tt)
      | PGet =>
        stmr0 <- trigger (PGet);;
        '(st0, _) <- (Any.split stmr0)ǃ;;
        Ret (fr0, st0)
      end
  .

  Definition massage_itr: itree Es ~> stateT Σ (itree Es') :=
    (* interp (case_ (massage_callE) (case_ (massage_rE) (case_ (massage_pE) trivial_state_Handler))) *)
    interp_state (case_ (massage_callE) (case_ (massage_rE) (case_ (massage_pE) trivial_state_Handler)))
  .

  Definition massage_fun (ktr: (mname * Any.t) -> itree Es Any.t): ((mname * Any.t) -> itree Es' Any.t) :=
    fun args => '(_, rv) <- massage_itr (ktr args) ε;; Ret rv
  .

  Definition massage_fsb: ((mname * Any.t) -> itree Es Any.t) -> fspecbody :=
    fun ktr => mk_specbody fspec_trivial (massage_fun ktr)
  .

  Definition massage (ms: ModSem.t): SModSem.t := {|
    SModSem.fnsems := List.map (map_snd massage_fsb) ms.(ModSem.fnsems);
    SModSem.mn := ms.(ModSem.mn);
    SModSem.initial_mr := ε;
    SModSem.initial_st := Any.pair (ms.(ModSem.initial_st)) (ε: Σ)↑;
  |}
  .

  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)

  Lemma massage_itr_bind
        (R S: Type)
        fr0 (s: itree _ R) (k : R -> itree _ S)
    :
      (massage_itr (s >>= k)) fr0
      =
      ((massage_itr s fr0) >>= (fun '(fr1, r) => massage_itr (k r) fr1)).
  Proof.
    unfold massage_itr in *. rewrite interp_state_bind. grind. des_ifs.
  Qed.

  Lemma massage_itr_tau
        (U: Type)
        (t : itree _ U) fr0
    :
      (massage_itr (tau;; t) fr0)
      =
      (tau;; (massage_itr t) fr0).
  Proof.
    unfold massage_itr in *. rewrite interp_state_tau. grind.
  Qed.

  Lemma massage_itr_ret
        (U: Type)
        (t: U) fr0
    :
      ((massage_itr (Ret t)) fr0)
      =
      Ret (fr0, t).
  Proof.
    unfold massage_itr in *. rewrite interp_state_ret. grind.
  Qed.

  Lemma massage_itr_triggerp
        (R: Type)
        (i: pE R) fr0
    :
      (massage_itr (trigger i) fr0)
      =
      (massage_pE i fr0 >>= (fun r => tau;; Ret r)).
  Proof.
    unfold massage_itr in *. rewrite interp_state_trigger. grind.
  Qed.

  Lemma massage_itr_triggere
        (R: Type)
        (i: eventE R) fr0
    :
      (massage_itr (trigger i) fr0)
      =
      (trigger i >>= (fun r => tau;; Ret (fr0, r))).
  Proof.
    unfold massage_itr in *. rewrite interp_state_trigger. grind. unfold trivial_state_Handler. grind.
  Qed.

  Lemma massage_itr_calle
        (R: Type)
        (i: callE R) fr0
    :
      (massage_itr (trigger i) fr0)
      =
      ((massage_callE i fr0) >>= (fun r => tau;; Ret r)).
  Proof.
    unfold massage_itr in *. grind.
  Qed.

  Lemma massage_itr_evente
        (R: Type)
        (i: eventE R) fr0
    :
      (massage_itr (trigger i) fr0)
      =
      ((trigger i) >>= (fun r => tau;; Ret (fr0, r))).
  Proof.
    unfold massage_itr in *. grind. unfold trivial_state_Handler. grind.
  Qed.

  Lemma massage_itr_triggerUB
        (R: Type) fr0
    :
      (massage_itr (triggerUB) fr0)
      =
      triggerUB (A:=(Σ * R)).
  Proof.
    unfold massage_itr, triggerUB in *. rewrite unfold_interp_state. cbn.
    unfold trivial_state_Handler. grind.
  Qed.

  Lemma massage_itr_triggerNB
        (R: Type) fr0
    :
      (massage_itr (triggerNB) fr0)
      =
      triggerNB (A:=(Σ * R)).
  Proof.
    unfold massage_itr, triggerNB in *. rewrite unfold_interp_state. cbn.
    unfold trivial_state_Handler. grind.
  Qed.

  Lemma massage_itr_unwrapU
        (R: Type)
        (i: option R) fr0
    :
      (massage_itr (unwrapU i) fr0)
      =
      r <- (unwrapU i);; Ret (fr0, r).
  Proof.
    unfold massage_itr, unwrapU in *. des_ifs.
    { etrans.
      { eapply massage_itr_ret. }
      { grind. }
    }
    { etrans.
      { eapply massage_itr_triggerUB. }
      { unfold triggerUB. grind. }
    }
  Qed.

  Lemma massage_itr_unwrapN
        (R: Type)
        (i: option R) fr0
    :
      (massage_itr (unwrapN i) fr0)
      =
      r <- (unwrapN i);; Ret (fr0, r).
  Proof.
    unfold massage_itr, unwrapN in *. des_ifs.
    { etrans.
      { eapply massage_itr_ret. }
      { grind. }
    }
    { etrans.
      { eapply massage_itr_triggerNB. }
      { unfold triggerNB. grind. }
    }
  Qed.

  Lemma massage_itr_assume
        P fr0
    :
      (massage_itr (assume P) fr0)
      =
      (assume P;;; tau;; Ret (fr0, tt))
  .
  Proof.
    unfold assume. rewrite massage_itr_bind. rewrite massage_itr_triggere. grind. eapply massage_itr_ret.
  Qed.

  Lemma massage_itr_guarantee
        P fr0
    :
      (massage_itr (guarantee P) fr0)
      =
      (guarantee P;;; tau;; Ret (fr0, tt)).
  Proof.
    unfold guarantee. rewrite massage_itr_bind. rewrite massage_itr_triggere. grind. eapply massage_itr_ret.
  Qed.

  Lemma massage_itr_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (massage_itr itr0)
      =
      (massage_itr itr1)
  .
  Proof. subst; et. Qed.

End MASSAGE.
End Massage.
Import Massage.

Section RDB.
  Context `{Σ: GRA.t}.

  Global Program Instance transl_itr_rdb: red_database (mk_box (@massage_itr)) :=
    mk_rdb
      0
      (mk_box massage_itr_bind)
      (mk_box massage_itr_tau)
      (mk_box massage_itr_ret)
      (mk_box massage_itr_calle)
      (mk_box massage_itr_triggere)
      (mk_box massage_itr_triggerp)
      (mk_box massage_itr_evente)
      (mk_box massage_itr_triggerUB)
      (mk_box massage_itr_triggerNB)
      (mk_box massage_itr_unwrapU)
      (mk_box massage_itr_unwrapN)
      (mk_box massage_itr_assume)
      (mk_box massage_itr_guarantee)
      (mk_box massage_itr_ext)
  .
End RDB.





Require Import SimModSemL.
Require Import SimModSemHint.
Require Import Hoare.
Require Import HTactics ProofMode.




Section ADQ.
  Context `{Σ: GRA.t}.

  Variable _kmds: list KMod.t.
  Let frds: Sk.t -> list mname := fun sk => (map (KModSem.mn ∘ (flip KMod.get_modsem sk)) _kmds).
  Let kmds: list SMod.t := List.map (KMod.transl frds) _kmds.
  Variable umds: list Mod.t.

  Let sk_link: Sk.t := Sk.sort (fold_right Sk.add Sk.unit ((List.map SMod.sk kmds) ++ (List.map Mod.sk umds))).
  Let skenv: SkEnv.t := Sk.load_skenv sk_link.

  Let _kmss: Sk.t -> list SModSem.t := fun ske => List.map (flip SMod.get_modsem ske) kmds.
  Let _umss: Sk.t -> list ModSem.t := fun ske => List.map (flip Mod.get_modsem ske) umds.
  Let _gstb: Sk.t -> list (gname * fspec) := fun ske =>
    (flat_map (List.map (map_snd fsb_fspec) ∘ SModSem.fnsems) (_kmss ske))
      ++ (flat_map (List.map (map_snd (fun _ => fspec_trivial)) ∘ ModSem.fnsems) (_umss ske)).

  Let kmss: list SModSem.t := Eval red in (_kmss sk_link).
  Let umss: list ModSem.t := Eval red in (_umss sk_link).
  Let gstb: list (gname * fspec) := Eval red in (_gstb sk_link).

  Lemma add_list_fnsems
        mds ske
    :
      (ModSemL.fnsems (ModL.get_modsem (Mod.add_list mds) ske)) =
      flat_map ModSemL.fnsems (List.map (flip ModL.get_modsem ske ∘ Mod.lift) mds)
  .
  Proof. induction mds; ss. f_equal. et. Qed.

  Ltac _list_tac :=
    match goal with
    | [ H: alist_find _ _ = Some _ |- _ ] => apply alist_find_some in H; des; des_sumbool; subst
    | [ H: context[ModL.enclose] |- _ ] => unfold ModL.enclose in H; try rewrite add_list_fnsems in H
    | [ H: In _ (flat_map _ _) |- _ ] => apply in_flat_map in H; des
    | [ H: In _ (List.map _ _) |- _ ] => apply in_map_iff in H; des
    | [ H: ModSem.map_snd _ _ = _ |- _ ] => unfold ModSem.map_snd in H; ss
    | [ H: map_snd _ _ = _ |- _ ] => unfold map_snd in H; ss
    | [ H: flip _ _ _ = _ |- _ ] => unfold flip in H; ss

    | [ |- context[ModL.enclose] ] => unfold ModL.enclose; try rewrite add_list_fnsems
    | [ |- In _ (flat_map _ _) ] => apply in_flat_map; esplits; et
    | [ |- In _ (List.map _ _) ] => apply in_map_iff; esplits; et
    | [ |- ModSem.map_snd _ _ = _ ] => unfold ModSem.map_snd; ss
    | [ |- map_snd _ _ = _ ] => unfold map_snd; ss
    | [ |- flip _ _ _ = _ ] => unfold flip; ss
    end
  .
  Ltac list_tac := repeat _list_tac.


  Lemma my_lemma1_aux'
        (ske: Sk.t) mrs (A: Type) (itr: itree Es A) (ctx: Σ)
        (WF: URA.wf (ctx ⋅ fst mrs)) fr
    :
      paco6
        (_sim_itree (fun '(st_src, st_tgt) => st_src = st_tgt))
        bot6
        (Σ * A)%type A
        (fun '(mrs_src, fr_src) '(mrs_tgt, fr_tgt) '(ctx, r_src) r_tgt => mrs_src = mrs_tgt /\ r_src = r_tgt
                                                                          /\ URA.wf (ctx ⋅ fst mrs_src))
        40%nat
        (mrs, fr, interp_hCallE_tgt (_gstb ske) ord_top (UModSem.massage_itr (_gstb ske) itr) ctx)
        (mrs, ε, UModSem.transl_itr (T:=A) itr)
  .
  Proof.
    ginit. revert mrs A itr ctx WF fr. gcofix CIH. i. ides itr.
    { steps. }
    { steps. gbase. eapply CIH; et. }
    rewrite <- bind_trigger.
    destruct e; cycle 1.
    {
      destruct s; ss.
      { destruct p; ss.
        - resub. ired_both. destruct mrs. gstep. econs; et. steps. gbase. eapply CIH; et.
        - resub. ired_both. destruct mrs. gstep. econs; et. steps. gbase. eapply CIH; et.
      }
      { destruct e; ss.
        - resub. ired_both. destruct mrs. gstep. econs; et.
          i. exists x_tgt. eexists. steps. gbase. eapply CIH; et.
        - resub. ired_both. destruct mrs. gstep. econs; et.
          i. exists x_src. eexists. steps. gbase. eapply CIH; et.
        - resub. ired_both. destruct mrs. gstep. econs; et.
          i. eexists. steps. gbase. eapply CIH; et.
      }
    }
    destruct u. resub. ired_both. steps. rewrite _UNWRAPU. steps.
    rename _UNWRAPU into T.
    eapply alist_find_some in T. unfold _gstb in T. rewrite in_app_iff in *. des; ss.
    - list_tac.
      des_ifs. unfold _kmss in T. list_tac. subst. unfold kmds in T0. list_tac. subst.
      ss. list_tac. des_ifs. ss.
      unfold HoareCall, discard, forge, put, checkWf. steps.
      destruct mrs.
      force_l. exists (c, ε). steps.
      force_l.
      { rewrite ! URA.unit_id. auto. }
      steps. force_l. exists ε. steps.
      force_l. exists ε. steps. force_l.
      { rewrite URA.unit_id. auto. }
      steps. force_l. exists None. steps.
      force_l. exists (args↑). steps.
      force_l. exists ord_top. steps.
      force_l.
      { rewrite Any.upcast_split. eapply to_semantic; [|eapply URA.wf_unit]. iIntros. iPureIntro. esplits; et. }
      steps. force_l.
      { split; et. }
      steps. gstep. econs; et. i. subst. destruct mrs_tgt1. eexists. steps.
      red in _ASSUME0. uipropall. subst.
      gbase. eapply CIH. ss.
      eapply URA.wf_mon. instantiate (1:=x0).
      replace (x2 ⋅ c0 ⋅ x0) with (x2 ⋅ (c0 ⋅ (ε ⋅ x0))); auto. r_solve.
    - list_tac.
      des_ifs. unfold _umss in T. list_tac. subst.
      unfold HoareCall, discard, forge, put, checkWf. steps.
      destruct mrs.
      force_l. exists (c, ε). steps.
      force_l.
      { rewrite ! URA.unit_id. auto. }
      steps. force_l. exists ε. steps.
      force_l. exists ε. steps. force_l.
      { rewrite URA.unit_id. auto. }
      steps. force_l. exists tt. steps.
      force_l. exists (args↑). steps.
      force_l. exists ord_top. steps.
      force_l.
      { eapply to_semantic; [|eapply URA.wf_unit]. iIntros. iPureIntro. esplits; et. }
      steps. force_l.
      { split; et. }
      steps. gstep. econs; et. i. subst. destruct mrs_tgt1. eexists. steps.
      red in _ASSUME0. uipropall. subst.
      gbase. eapply CIH. ss.
      eapply URA.wf_mon. instantiate (1:=x).
      replace (x2 ⋅ c0 ⋅ x) with (x2 ⋅ (c0 ⋅ (ε ⋅ x))); auto. r_solve.
    Unshelve.
    all: try (exact Ord.O).
    all: try (exact 0%nat).
  Qed.

  Ltac r_wf H := eapply prop_ext_rev; [eapply f_equal|]; [|eapply H]; r_solve.

  Lemma my_lemma1_aux
        mrs ktr arg ske
    :
      sim_itree (fun '(x, y) => x = y) 100%nat
                (mrs, ε, fun_to_tgt (_gstb ske) (UModSem.massage_fsb (_gstb ske) ktr) arg)
                (mrs, ε, (UModSem.transl_fun ktr) arg)
  .
  Proof.
    destruct mrs as [mr st].
    unfold fun_to_tgt, UModSem.transl_fun, HoareFun, discard, forge, checkWf, put, cfun.
    ginit. steps. red in _ASSUME0. uipropall. des. clarify.
    unfold UModSem.massage_fun.
    guclo lordC_spec. econs.
    { instantiate (1:=(49 + 40)%ord). rewrite <- OrdArith.add_from_nat. eapply OrdArith.le_from_nat. lia. }
    erewrite idK_spec with (i0:=UModSem.transl_itr (ktr arg)).
    guclo lbindC_spec. econs.
    { gfinal. right. eapply my_lemma1_aux'.
      eapply URA.wf_mon. instantiate (1:=x2). r_wf _ASSUME. }
    i. destruct st_src1, st_tgt1. destruct vret_src. ss. des; subst. destruct p0.
    force_l. eexists. force_l. eexists (_, _). steps.
    force_l.
    { instantiate (1:=ε). instantiate (1:=c2). r_wf SIM1. }
    steps. force_l. eexists.
    force_l.
    { red. uipropall. }
    steps. force_l. eexists. force_l.
    { instantiate (1:=ε). instantiate (1:=ε). rewrite URA.unit_id. auto. }
    steps.
    (* can not Qed bcz of Coq bug... *)
  Admitted.

  Lemma my_lemma1
        umd
        (IN: In umd umds)
    :
      ModPair.sim (SMod.to_tgt _gstb (UMod.massage _gstb umd)) (UMod.transl umd)
  .
  Proof.
    econs; ss.
    i. r. econs.
    { instantiate (1:=fun '(x, y) => x = y). ss.
      set (ums:=UMod.get_modsem umd sk) in *.
      rewrite ! List.map_map.
      eapply Forall2_apply_Forall2.
      { refl. }
      i. subst. unfold map_snd. des_ifs.
      rr. split; ss. r. ii. subst. ss. esplits; et. eapply my_lemma1_aux.
    }
    { ss. }
    { ss. }
  Qed.

  Let ns := mk_sk_gnames (fun sk => mk_gnames (fun fn => is_some (alist_find fn (_gstb sk)))).
  Local Existing Instances ns.

  Lemma my_lemma2_aux
        sk mrs ktr arg
    :
      sim_itree (ns:= sk_gnames_contents sk) (fun '(x, y) => x = y) 100%nat
                (mrs, ε, (UModSem.transl_fun ktr) arg)

  (mrs, ε, fun_to_src (fsb_body (UModSem.massage_fsb (_gstb sk) ktr)) arg)
  .
  Proof.
    destruct mrs as [mr st]. ss.
    unfold fun_to_src, UModSem.transl_fun, UModSem.massage_fun, body_to_src.
    ginit. abstr (ktr arg) itr. clear ktr arg. revert_until gstb. gcofix CIH. i.
    ides itr.
    { steps. }
    { steps. gbase. eapply CIH; et. }
    rewrite <- bind_trigger.
    destruct e; cycle 1.
    {
      destruct s; ss.
      { destruct p; ss.
        - resub. ired_both. gstep; econs; eauto. steps. gbase. eapply CIH; et.
        - resub. ired_both. gstep; econs; eauto. steps. gbase. eapply CIH; et.
      }
      { destruct e; ss.
        - resub. ired_both. gstep; econs; et. i. esplits; et. steps. gbase. eapply CIH; et.
        - resub. ired_both. gstep; econs; et. i. esplits; et. steps. gbase. eapply CIH; et.
        - resub. ired_both. gstep; econs; et. i. esplits; et. steps. gbase. eapply CIH; et.
      }
    }
    destruct u. resub. ired_both. unfold unwrapU. des_ifs.
    { steps. gstep. econs; ss. i. subst. destruct mrs_tgt1. esplits. steps.
      gbase. eapply CIH. }
    { gstep; econs; eauto. ss. ii. rewrite Heq in *. ss. }
  Unshelve.
    all: try (exact Ord.O).
  Qed.

  Lemma my_lemma2
        (umd: UMod.t)
        (IN: In umd umds)
    :
      ModPair.sim (UMod.transl umd) (SMod.to_src (UMod.massage _gstb umd))
  .
  Proof.
    econs; ss.
    i. r. econs.
    { instantiate (1:=fun '(x, y) => x = y). ss.
      set (ums:=UMod.get_modsem umd sk) in *.
      rewrite ! List.map_map.
      eapply Forall2_apply_Forall2.
      { refl. }
      i. subst. unfold map_snd. des_ifs.
      rr. split; ss. r. ii. subst. ss. esplits; et.
      eapply my_lemma2_aux.
    }
    { ss. }
    { ss. }
  Qed.

  Ltac steps := HoareDef.steps.


  Declare Scope l_monad_scope.
  Local Open Scope l_monad_scope.
  Notation "'do' X <- A ; B" := (List.flat_map (fun X => B) A) : l_monad_scope.
  Notation "'do' ' X <- A ; B" := (List.flat_map (fun _x => match _x with | X => B end) A) : l_monad_scope.
  Notation "'ret'" := (fun X => [X]) (at level 60) : l_monad_scope.

  Lemma gstb_eq: forall ske,
    _gstb ske =
    (List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec)))
       (flat_map SModSem.fnsems
          (List.map
             (flip SMod.get_modsem ske)
             (kmds ++ List.map (UMod.massage _gstb) umds))))
  .
  Proof.
    i. unfold _gstb.
    unfold _kmss, _umss.
    rewrite map_app. rewrite flat_map_app. rewrite map_app.
    f_equal.
    - rewrite <- ! SMod.red_do_ret. erewrite ! SMod.flat_map_assoc. ss.
    - rewrite <- ! SMod.red_do_ret. erewrite ! SMod.flat_map_assoc.
      eapply flat_map_ext. intro umd. unfold flip. ss.
      rewrite <- ! SMod.red_do_ret. erewrite ! SMod.flat_map_assoc. rewrite ! List.app_nil_r.
      eapply flat_map_ext. intro. unfold map_snd. des_ifs.
  Qed.

  Definition UMod_main (mainbody: Any.t -> itree (uCallE +' pE +' eventE) Any.t): UMod.t := {|
    UMod.get_modsem := fun _ => (UModSem.mk [("main", mainbody)] "Main" (tt↑));
    UMod.sk := Sk.unit;
  |}
  .

  Variable (mainbody: Any.t -> itree (uCallE +' pE +' eventE) Any.t).
  Hypothesis MAINU: In (UMod_main mainbody) umds.

  Let mains: SMod.t := UMod.massage _gstb (UMod_main mainbody).

  Hypothesis WFR: URA.wf (List.fold_left (⋅) (List.map (SModSem.initial_mr) kmss) ε).
  (* Hypothesis MAINM: In (SMod.main mainpre mainbody) kmds. *)

  Theorem adequacy_open:
    refines_closed (Mod.add_list (List.map (SMod.to_tgt _gstb) kmds ++ List.map UMod.transl umds))
                   (Mod.add_list (List.map (SMod.to_src) kmds ++ List.map UMod.transl umds))
  .
  Proof.
    etrans.
    { eapply refines_close.
      rewrite Mod.add_list_app.
      eapply refines_proper_l.
      eapply adequacy_local_list.
      instantiate (1:=(List.map (SMod.to_tgt _gstb ∘ (UMod.massage _gstb)) umds)).
      eapply Forall2_apply_Forall2.
      { instantiate (1:=eq). refl. }
      i. subst. eapply my_lemma1; ss.
    }
    rewrite <- Mod.add_list_app.
    etrans.
    { erewrite <- List.map_map with (f:=UMod.massage _gstb).
      rewrite <- map_app.
      eapply adequacy_type2.
      - instantiate (1:=(kmds ++ List.map (UMod.massage _gstb) umds)).
        erewrite <- List.map_id with (l:=(kmds ++ List.map (UMod.massage _gstb) umds)) at 1.
        eapply Forall2_apply_Forall2.
        { instantiate (1:=eq). refl. }
        i. subst. exists _gstb. split; ss. r. intro ske. rewrite <- gstb_eq. refl.
      - admit "main pre".
      - ss. instantiate (1:=ε). rewrite ! URA.unit_id. rewrite ! URA.unit_idl. admit "should be ez".
      - Check (UModSem.massage_fun gstb mainbody).
        admit "mid - main argument parameterization".
        (* instantiate (1:=UModSem.transl_fun_smod mainbody). rewrite in_app_iff. eauto. *)
    }
    etrans.
    { instantiate (1:=Mod.add_list ((map SMod.to_src kmds) ++ (List.map (UMod.transl) umds))). eapply adequacy_hint.
      { clear. i. unfold ns. ss. unfold _gstb.
        rewrite Mod.add_list_app in SOME. ss.
        unfold _kmss, _umss. clear - SOME.
        rewrite add_list_fnsems in *. rewrite List.map_map in *.
        assert (is_some (alist_find fn ((do X <- map (fun x => flip ModL.get_modsem sk (SMod.to_src x)) kmds; ModSemL.fnsems X)))
                ->
                is_some (alist_find fn ((do x <- map (flip SMod.get_modsem sk) kmds; map (map_snd fsb_fspec) (SModSem.fnsems x))))).
        { clear. generalize kmds.
          induction kmds0; ss.
          change ModSem.map_snd with map_snd.
          rewrite ! alist_find_app_o in *. rewrite ! alist_find_map_snd in *.
          change (fun '(fn0, sb) => (fn0, fun_to_src (fsb_body sb))) with (@map_snd string _ _ (fun_to_src ∘ fsb_body)).
          uo. des_ifs. rewrite alist_find_map_snd in Heq2.
          rewrite Heq1 in *. ss.
        }
        assert (is_some (alist_find fn (ModSemL.fnsems (ModL.get_modsem (Mod.add_list (map UMod.transl umds)) sk)))
                ->
                is_some (alist_find fn (do x <- map (flip UMod.get_modsem sk) umds;
                                           map (map_snd (fun _ => fspec_trivial)) (UModSem.fnsems x)))).
        { clear. generalize umds.
          induction umds0; ss.
          change ModSem.map_snd with map_snd.
          rewrite ! alist_find_app_o in *. rewrite ! alist_find_map_snd in *. uo. des_ifs. }
        rewrite ! alist_find_app_o in *. des_ifs; et. exfalso. ss. intuition.
      }
      rewrite ! List.map_app. eapply Forall2_app.
      { eapply Forall2_apply_Forall2.
        { instantiate (1:=eq). refl. }
        { i. subst. eapply ModPair.self_sim. }
      }
      { rewrite List.map_map. eapply Forall2_apply_Forall2.
        { instantiate (1:=eq). refl. }
        { i. subst. eapply my_lemma2. auto. }
      }
    }
    rewrite Mod.add_list_app. refl.
  Unshelve.
    all: ss.
    { ii. apply True. }
    { ii. apply ITree.spin. }
  Qed.

End ADQ.
