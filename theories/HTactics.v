Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef SimModSem.

From ExtLib Require Import
     Data.Map.FMapAList.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.

Hint Resolve sim_itree_mon: paco.
Hint Resolve cpn3_wcompat: paco.

Ltac anytac := (try rewrite ! Any.upcast_downcast in *); clarify; apply_all_once Any.upcast_inj; des; clarify; clear_tac.

Ltac asimpl := try (unfold alist_add, alist_remove in *); ss.


Section HOARE.
  Let Any_tgt := Any.t.
  Notation Es' := (hCallE +' pE +' eventE).
  Context `{Σ: GRA.t}.
  Variable stb: list (gname * fspec).

  Definition HoareFunArg
             (mn: mname)
             {X Y: Type}
             (P: X -> Y -> Any_tgt -> ord -> Σ -> Prop): Any_tgt -> itree Es (X * Y * ord) := fun varg_tgt =>
    varg_src <- trigger (Take Y);;
    x <- trigger (Take X);;
    rarg <- trigger (Take Σ);; forge rarg;; (*** virtual resource passing ***)
    (checkWf mn);;
    ord_cur <- trigger (Take _);;
    assume(P x varg_src varg_tgt ord_cur rarg);; (*** precondition ***)
    Ret (x, varg_src, ord_cur)
  .

  Definition HoareFunRet
             (mn: mname)
             {X Z: Type}
             (Q: X -> Z -> Any_tgt -> Σ -> Prop): X -> Z -> itree Es Any_tgt := fun x vret_src =>
    vret_tgt <- trigger (Choose Any_tgt);;
    '(mret, fret) <- trigger (Choose _);; put mn mret fret;; (*** updating resources in an abstract way ***)
    rret <- trigger (Choose Σ);; guarantee(Q x vret_src vret_tgt rret);; (*** postcondition ***)
    (discard rret);; (*** virtual resource passing ***)

    Ret vret_tgt (*** return ***)
  .

  Lemma HoareFun_parse
        (mn: mname)
        {X Y Z: Type}
        (P: X -> Y -> Any_tgt -> ord -> Σ -> Prop)
        (Q: X -> Z -> Any_tgt -> Σ -> Prop)
        (body: Y -> itree Es' Z)
        (varg_tgt: Any_tgt)
    :
      HoareFun stb mn P Q body varg_tgt =
      '(x, varg_src, ord_cur) <- HoareFunArg mn P varg_tgt;;
      vret_src <- match ord_cur with
                  | ord_pure n => (interp_hCallE_tgt stb mn ord_cur APC);; trigger (Choose _)
                  | _ => (interp_hCallE_tgt stb mn ord_cur (body varg_src))
                  end;;
      HoareFunRet mn Q x vret_src.
  Proof.
    unfold HoareFun, HoareFunArg, HoareFunRet, body_to_tgt.
    ired. repeat f_equal.
    extensionality y. ired. repeat f_equal.
    extensionality x. ired. repeat f_equal.
    extensionality rarg. ired. repeat f_equal.
    extensionality u0. ired. repeat f_equal.
    extensionality u1. ired. repeat f_equal.
    extensionality ord_cur. ired. repeat f_equal.
  Qed.
End HOARE.


Ltac init :=
  split; ss; ii; clarify; rename y into varg; eexists 100%nat; ss; des; clarify;
  ginit; asimpl;
  try (unfold fun_to_tgt, cfun; rewrite HoareFun_parse); ss.

Lemma sim_l_bind_bind `{Σ: GRA.t} a b c d e f g
      (R S : Type) (s : itree _ R) (k : R -> itree _ S) (h : S -> itree _ _)
      (SIM: gpaco3 (_sim_itree c) d e f g (b, ` r : R <- s;; ` x : _ <- k r;; h x) a)
  :
    gpaco3 (_sim_itree c) d e f g (b, ` x : _ <- (` x : _ <- s;; k x);; h x) a.
Proof.
  rewrite bind_bind. auto.
Qed.

Lemma sim_l_bind_tau `{Σ: GRA.t} a b c d e f g
      (U : Type) (t : itree _ _) (k : U -> itree _ _)
      (SIM: gpaco3 (_sim_itree c) d e f g (b, Tau (` x : _ <- t;; k x)) a)
  :
    gpaco3 (_sim_itree c) d e f g (b, ` x : _ <- Tau t;; k x) a.
Proof.
  rewrite bind_tau. auto.
Qed.

Lemma sim_l_bind_ret_l `{Σ: GRA.t} a b c d e f g
      (R : Type) (r : R) (k : R -> itree _ _)
      (SIM: gpaco3 (_sim_itree c) d e f g (b, k r) a)
  :
    gpaco3 (_sim_itree c) d e f g (b, ` x : _ <- Ret r;; k x) a.
Proof.
  rewrite bind_ret_l. auto.
Qed.

Lemma sim_r_bind_bind `{Σ: GRA.t} a b c d e f g
      (R S : Type) (s : itree _ R) (k : R -> itree _ S) (h : S -> itree _ _)
      (SIM: gpaco3 (_sim_itree c) d e f g a (b, ` r : R <- s;; ` x : _ <- k r;; h x))
  :
    gpaco3 (_sim_itree c) d e f g a (b, ` x : _ <- (` x : _ <- s;; k x);; h x).
Proof.
  rewrite bind_bind. auto.
Qed.

Lemma sim_r_bind_tau `{Σ: GRA.t} a b c d e f g
      (U : Type) (t : itree _ _) (k : U -> itree _ _)
      (SIM: gpaco3 (_sim_itree c) d e f g a (b, Tau (` x : _ <- t;; k x)))
  :
    gpaco3 (_sim_itree c) d e f g a (b, ` x : _ <- Tau t;; k x).
Proof.
  rewrite bind_tau. auto.
Qed.

Lemma sim_r_bind_ret_l `{Σ: GRA.t} a b c d e f g
      (R : Type) (r : R) (k : R -> itree _ _)
      (SIM: gpaco3 (_sim_itree c) d e f g a (b, k r))
  :
    gpaco3 (_sim_itree c) d e f g a (b, ` x : _ <- Ret r;; k x).
Proof.
  rewrite bind_ret_l. auto.
Qed.

Ltac interp_red := rewrite interp_vis ||
                           rewrite interp_ret ||
                           rewrite interp_tau ||
                           rewrite interp_trigger ||
                           rewrite interp_bind.

Ltac interp_mrec_red := rewrite interp_mrec_hit ||
                                rewrite interp_mrec_miss ||
                                rewrite interp_mrec_bind ||
                                rewrite interp_mrec_tau ||
                                rewrite interp_mrec_ret.

Ltac interp_state_red := rewrite interp_state_trigger ||
                                 rewrite interp_state_bind ||
                                 rewrite interp_state_tau ||
                                 rewrite interp_state_ret.

Ltac ired_l :=
  cbn;
  match goal with
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, ITree.bind' _ (ITree.bind' _ _)) _) ] =>
    apply sim_l_bind_bind; ired_l
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, ITree.bind' _ (Tau _)) _) ] =>
    apply sim_l_bind_tau
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, ITree.bind' _ (Ret _)) _) ] =>
    apply sim_l_bind_ret_l; ired_l
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, interp _ _) _) ] =>
    ((interp_red; ired_l) || idtac)
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, ITree.bind' _ (interp _ _)) _) ] =>
    ((interp_red; ired_l) || idtac)
  | _ => idtac
  end.

Ltac ired_r :=
  cbn;
  match goal with
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ _ (_, ITree.bind' _ (ITree.bind' _ _))) ] =>
    apply sim_r_bind_bind; ired_r
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ _ (_, ITree.bind' _ (Tau _))) ] =>
    apply sim_r_bind_tau
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ _ (_, ITree.bind' _ (Ret _))) ] =>
    apply sim_r_bind_ret_l
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ _ (_, interp _ _)) ] =>
    ((interp_red; ired_r) || idtac)
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ _ (_, ITree.bind' _ (interp _ _))) ] =>
    ((interp_red; ired_r) || idtac)
  | _ => idtac
  end.

Ltac ired_all := ired_l; ired_r.

Ltac prep := ired_all.

Ltac force_l :=
  prep;
  match goal with
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, guarantee ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_all; gstep; eapply sim_itree_choose_src; [eauto|exists name]|contradict name]; cycle 1

  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_tgt; gstep; econs; eauto; unseal i_tgt
  end
.
Ltac force_r :=
  prep;
  match goal with
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    destruct (classic P) as [name|name]; [ired_all; gstep; eapply sim_itree_take_tgt; [eauto|exists name]|contradict name]; cycle 1

  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_src; gstep; econs; eauto; unseal i_src
  end
.

Ltac _step :=
  match goal with
  (*** blacklisting ***)
  (* | [ |- (gpaco3 (_sim_itree wf) _ _ _ _ (_, trigger (Choose _) >>= _) (_, ?i_tgt)) ] => idtac *)
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_all; _step; ss; fail]
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    ired_all; gstep; eapply sim_itree_take_src; [apply Nat.lt_succ_diag_r|]; intro name

  (*** blacklisting ***)
  (* | [ |- (gpaco3 (_sim_itree wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_all; _step; ss; fail]
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    ired_all; gstep; eapply sim_itree_choose_tgt; [apply Nat.lt_succ_diag_r|]; intro name



  | _ => (*** default ***)
    gstep; econs; try apply Nat.lt_succ_diag_r; i
  end;
  (* idtac *)
  match goal with
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end
.
Ltac steps := repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) unfold alist_add; simpl; des_ifs_safe).

Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 tgt1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco3 (_sim_itree wf) _ _ _ n (([(_, src0)], src1), src2) (([(_, tgt0)], tgt1), tgt2))
      (at level 60,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' tgt1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Section HLEMMAS.
  Context `{Σ: GRA.t}.
  Local Opaque GRA.to_URA.

  Lemma hcall_clo
        X (x: X) (o: ord)
        (mr_src1 fr_src1 rarg_src: Σ)
        r rg (n: nat) mr_src0 mp_src0 fr_src0 Y Z
        (P: X -> Y -> Any.t -> ord -> Σ -> Prop)
        (Q: X -> Z -> Any.t -> Σ -> Prop)
        mrs_tgt frs_tgt k_tgt k_src
        mn fn tbr ord_cur varg_src varg_tgt
        (wf: (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)) -> Prop)

        (UPDATABLE: URA.updatable (URA.add mr_src0 fr_src0) (URA.add mr_src1 (URA.add rarg_src fr_src1)))
        (FUEL: n > 15)
        (PRE: P x varg_src varg_tgt o rarg_src)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))
        (WF: wf ([(mn, (mr_src1, mp_src0))], mrs_tgt))
        (POST: forall (vret_tgt : Any.t) (mrs_src1 mrs_tgt1 : alist string (Σ * Any.t))
                      (rret: Σ) (vret_src: Z)
                      (WF: wf (mrs_src1, mrs_tgt1)),
            exists (mr_src2: Σ) (mp_src2: Any.t),
              (<<LOOKUP: lookup mn mrs_src1 = Some (mr_src2, mp_src2)>>) /\
              forall (VALID: URA.wf (URA.add mr_src2 (URA.add fr_src1 rret)))
                     (POST: Q x vret_src vret_tgt rret),
                gpaco3 (_sim_itree wf) (cpn3 (_sim_itree wf)) rg rg 100
                       (mrs_src1, URA.add fr_src1 rret, k_src vret_src) (mrs_tgt1, frs_tgt, k_tgt vret_tgt))
    :
      gpaco3 (_sim_itree wf) (cpn3 (_sim_itree wf)) r rg n
             (([(mn, (mr_src0, mp_src0))], fr_src0),
              (HoareCall mn tbr ord_cur P Q fn varg_src) >>= k_src)
             ((mrs_tgt, frs_tgt),
              trigger (Call fn varg_tgt) >>= k_tgt).
  Proof.
    unfold HoareCall, put, discard, forge, checkWf, assume, guarantee.
    ired. gstep. econs; eauto. exists (mr_src1, URA.add rarg_src fr_src1).
    ired. gstep. econs; eauto.
    { instantiate (1:=mp_src0). instantiate (1:=mr_src0). admit "ez". }
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto. split; auto.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto.
    { instantiate (1:=mp_src0). instantiate (1:=mr_src0). admit "ez". }
    ired. gstep. econs; eauto. exists rarg_src.
    ired. gstep. econs; eauto.
    replace (alist_add Dec_RelDec mn (mr_src1, mp_src0) [(mn, (mr_src0, mp_src0))]) with [(mn, (mr_src1, mp_src0))].
    2: { admit "ez". }
    ired. gstep. econs; eauto. exists fr_src1.
    ired. gstep. econs; eauto. split; auto.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto. exists x.
    ired. gstep. econs; eauto. exists varg_tgt.
    ired. gstep. econs; eauto. exists o.
    ired. gstep. econs; eauto. split; auto.
    ired. gstep. econs; eauto. split; auto.
    ired. gstep. econs; eauto. i. exists 108.
    ired. gstep. econs; eauto. i.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto. i.
    hexploit (POST vret mrs_src1 mrs_tgt1 x0 x1 WF0). i. des.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto. i.
    ired. gstep. econs; eauto.
  Qed.

  Lemma harg_clo
        r rg mr_src0 mp_src0 fr_src0
        mn X Y (P: X -> Y -> Any.t -> ord -> Σ -> Prop) varg_tgt
        mrs_tgt frs_tgt f_tgt k_src
        (wf: (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)) -> Prop)
        (ARG:
           forall x varg_src rarg_src ord_cur
                  (VALID: URA.wf (URA.add mr_src0 (URA.add fr_src0 rarg_src)))
                  (PRE: P x varg_src varg_tgt ord_cur rarg_src),
             gpaco3 (_sim_itree wf) (cpn3 (_sim_itree wf)) rg rg 90
                    ([(mn, (mr_src0, mp_src0))], URA.add fr_src0 rarg_src,
                     k_src (x, varg_src, ord_cur)) (mrs_tgt, frs_tgt, f_tgt))
    :
      gpaco3 (_sim_itree wf) (cpn3 (_sim_itree wf)) r rg 100
             (([(mn, (mr_src0, mp_src0))], fr_src0),
              (HoareFunArg mn P varg_tgt >>= k_src))
             ((mrs_tgt, frs_tgt),
              f_tgt).
  Proof.
    unfold HoareFunArg, put, discard, forge, checkWf, assume, guarantee.
    ired. gstep. econs; eauto. intros varg_src.
    ired. gstep. econs; eauto. intros x.
    ired. gstep. econs; eauto. intros rarg_src.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto.
    { instantiate (1:=mp_src0). instantiate (1:=mr_src0). admit "ez". }
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto. intros VALID.
    ired. gstep. econs; eauto. intros ord_cur.
    ired. gstep. econs; eauto.
  Qed.

  Lemma hret_clo (mr_src1 rret_src: Σ)
        r rg n mr_src0 mp_src0 fr_src0
        mn X Z (Q: X -> Z -> Any.t -> Σ -> Prop)
        x vret_src vret_tgt
        mrs_tgt frs_tgt
        (wf: (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)) -> Prop)
        (FUEL: n > 14)
        (UPDATABLE: URA.updatable (URA.add mr_src0 fr_src0) (URA.add mr_src1 rret_src))
        (POST: Q x vret_src vret_tgt rret_src)
        (WF: wf ([(mn, (mr_src1, mp_src0))], mrs_tgt))
    :
      gpaco3 (_sim_itree wf) (cpn3 (_sim_itree wf)) r rg n
             (([(mn, (mr_src0, mp_src0))], fr_src0),
              (HoareFunRet mn Q x vret_src))
             ((mrs_tgt, frs_tgt),
              (Ret vret_tgt)).
  Proof.
    unfold HoareFunRet, put, discard, forge, checkWf, assume, guarantee.
    ired. gstep. econs; eauto. exists vret_tgt.
    ired. gstep. econs; eauto. exists (mr_src1, rret_src).
    ired. gstep. econs; eauto.
    { instantiate (1:=mp_src0). instantiate (1:=mr_src0). admit "ez". }
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto. split; auto.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto.
    { instantiate (1:=mp_src0). instantiate (1:=mr_src0). admit "ez". }
    ired. gstep. econs; eauto. exists rret_src.
    ired. gstep. econs; eauto. split; auto.
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto. exists ε.
    ired. gstep. econs; eauto. split.
    { rewrite URA.unit_id. auto. }
    ired. gstep. econs; eauto.
    ired. gstep. econs; eauto.
    replace (alist_add Dec_RelDec mn (mr_src1, mp_src0) [(mn, (mr_src0, mp_src0))]) with [(mn, (mr_src1, mp_src0))].
    2: { admit "ez". }
    auto.
  Qed.
End HLEMMAS.

Ltac harg_tac := prep; eapply harg_clo; i.

Ltac hcall_tac x o mr_src1 fr_src1 rarg_src := prep; eapply (@hcall_clo _ _ x o mr_src1 fr_src1 rarg_src); [|lia|..].

Ltac hret_tac mr_src1 rret_src := prep; eapply (@hret_clo _ mr_src1 rret_src); [lia|..].
