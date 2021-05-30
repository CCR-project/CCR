Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Import ModSemL.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef.
Require Import SimSTS.
Require Import SimGlobal.
Require Import HoareDef.
From Ordinal Require Import Ordinal Arithmetic.

Set Implicit Arguments.
















Inductive _simg_safe (simg: forall R0 R1 (RR: R0 -> R1 -> Prop), Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop) (i0: Ord.t): (itree eventE R0) -> (itree eventE R1) -> Prop :=
| simg_safe_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    _simg_safe simg RR i0 (Ret r_src) (Ret r_tgt)
| simg_safe_syscall
    i1 ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR i1 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg_safe simg RR i0 (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)



| simg_safe_tau
    i1 itr_src0 itr_tgt0
    (TAUBOTH: True)
    (* (ORD: Ordinal.le i1 i0) *)
    (SIM: simg _ _ RR i1 itr_src0 itr_tgt0)
  :
    _simg_safe simg RR i0 (tau;; itr_src0) (tau;; itr_tgt0)
| simg_safe_tauL
    i1 itr_src0 itr_tgt0
    (TAUL: True)
    (ORD: Ord.lt i1 i0)
    (SIM: simg _ _ RR i1 itr_src0 itr_tgt0)
  :
    _simg_safe simg RR i0 (tau;; itr_src0) (itr_tgt0)
| simg_safe_tauR
    i1 itr_src0 itr_tgt0
    (TAUR: True)
    (ORD: Ord.lt i1 i0)
    (SIM: simg _ _ RR i1 itr_src0 itr_tgt0)
  :
    _simg_safe simg RR i0 (itr_src0) (tau;; itr_tgt0)



| simg_safe_chooseR
    i1 X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (ORD: Ord.lt i1 i0)
    (SIM: forall x, simg _ _ RR i1 itr_src0 (ktr_tgt0 x))
  :
    _simg_safe simg RR i0 (itr_src0) (trigger (Choose X) >>= ktr_tgt0)



| simg_safe_takeL
    i1 X ktr_src0 itr_tgt0
    (TAKEL: True)
    (ORD: Ord.lt i1 i0)
    (SIM: forall x, simg _ _ RR i1 (ktr_src0 x) itr_tgt0)
  :
    _simg_safe simg RR i0 (trigger (Take X) >>= ktr_src0) (itr_tgt0)



(* | simg_stutter *)
(*     i1 itr_src itr_tgt *)
(*     (ORD: Ord.lt i1 i0) *)
(*     (SIM: simg _ RR i1 itr_src itr_tgt) *)
(*   : *)
(*     simg_safe simg RR i0 itr_src itr_tgt *)
.

Lemma simg_safe_spec:
  _simg_safe <7= _simg.
Proof. i. inv PR; try by (econs; eauto). Qed.


















(* Program Instance ord_lt_proper: Proper (Ord.eq ==> Ord.eq ==> eq) Ord.lt. *)
(* Next Obligation. *)
(*   ii. *)
(*   apply prop_ext. split; i. *)
(*   - eapply Ord.lt_eq_lt. { sym. et. } eapply Ord.eq_lt_lt; et. sym. et. *)
(*   - eapply Ord.lt_eq_lt; et. eapply Ord.eq_lt_lt; et. *)
(* Qed. *)

Program Instance lt_proper: Proper (Ord.eq ==> Ord.eq ==> iff) (Ord.lt).
Next Obligation.
  ii.
  split; i.
  - eapply Ord.lt_eq_lt. { sym. et. } eapply Ord.eq_lt_lt; et. sym. et.
  - eapply Ord.lt_eq_lt; et. eapply Ord.eq_lt_lt; et.
Qed.

Program Instance le_proper: Proper (Ord.eq ==> Ord.eq ==> iff) (Ord.le).
Next Obligation.
  ii.
  split; i.
  - eapply Ord.le_eq_le. { sym. et. } eapply Ord.eq_le_le; et. sym. et.
  - eapply Ord.le_eq_le; et. eapply Ord.eq_le_le; et.
Qed.

Program Instance expn_proper: Proper (Ord.eq ==> Ord.eq ==> Ord.eq) (OrdArith.expn).
Next Obligation.
  ii.
  etrans.
  - eapply OrdArith.eq_expn_l; et.
  - eapply OrdArith.eq_expn_r; et.
Qed.

Program Instance expn_le_proper: Proper (Ord.le ==> Ord.le ==> Ord.le) (OrdArith.expn).
Next Obligation.
  ii.
  etrans.
  - eapply OrdArith.le_expn_l; et.
  - eapply OrdArith.le_expn_r; et.
Qed.

Program Instance add_proper: Proper (Ord.eq ==> Ord.eq ==> Ord.eq) (OrdArith.add).
Next Obligation.
  ii.
  etrans.
  - eapply OrdArith.eq_add_l; et.
  - eapply OrdArith.eq_add_r; et.
Qed.

Program Instance add_le_proper: Proper (Ord.le ==> Ord.le ==> Ord.le) (OrdArith.add).
Next Obligation.
  ii.
  etrans.
  - eapply OrdArith.le_add_l; et.
  - eapply OrdArith.le_add_r; et.
Qed.

(* Program Instance add_lt_proper: Proper (Ord.le ==> Ord.lt ==> Ord.lt) (OrdArith.add). *)
(* Next Obligation. *)
(*   ii. *)
(*   eapply Ord.le_lt_lt. *)
(*   - rewrite H. refl. *)
(*   - eapply OrdArith.lt_add_r; et. *)
(* Qed. *)

Program Instance mult_eq_proper: Proper (Ord.eq ==> Ord.eq ==> Ord.eq) (OrdArith.mult).
Next Obligation.
  ii.
  etrans.
  - eapply OrdArith.eq_mult_l; et.
  - eapply OrdArith.eq_mult_r; et.
Qed.

Program Instance mult_le_proper: Proper (Ord.le ==> Ord.le ==> Ord.le) (OrdArith.mult).
Next Obligation.
  ii.
  etrans.
  - eapply OrdArith.le_mult_l; et.
  - eapply OrdArith.le_mult_r; et.
Qed.

Program Instance S_proper: Proper (Ord.eq ==> Ord.eq) (Ord.S).
Next Obligation.
  ii.
  eapply Ord.eq_S; et.
Qed.

(* Program Instance eq_proper: Proper (Ord.eq ==> Ord.eq ==> Ord.eq) (Ord.lt). *)
(* Next Obligation. *)
(*   ii. *)
(*   split; i. *)
(*   - eapply Ord.lt_eq_lt. { sym. et. } eapply Ord.eq_lt_lt; et. sym. et. *)
(*   - eapply Ord.lt_eq_lt; et. eapply Ord.eq_lt_lt; et. *)
(* Qed. *)

(* Theorem ord_pow_one: forall o0, (o0 ^ 1 == o0)%ord. *)
(* Proof. *)
(*   i. *)
(*   unfold OrdArith.expn. *)
(*   rewrite <- (OrdArith.add_O_r 1%ord). *)
(*   rewrite OrdArith.expn_add. *)
(*   replace (Ord.from_nat 1) with (1 + 0)%ord; cycle 1. *)
(*   { rewrite OrdArith.add_O_r. Ord.add_0_r. *)
(*   Set Printing All. *)
(*   ss. *)
(*   replace (1%ord) with (Ord.O + (1%ord))%ord. by ss. *)
(*   etrans. rewrite OrdArith.expn_add. *)
(* Qed. *)

Lemma add_le_lt: forall x0 x1 y0 y1, (x0 <= x1)%ord -> (y0 < y1)%ord -> (x0 + y0 < x1 + y1)%ord.
Proof.
  i.
  eapply Ord.le_lt_lt.
  - eapply OrdArith.le_add_l; et.
  - eapply OrdArith.lt_add_r; et.
Qed.

Lemma add_le_le: forall x0 x1 y0 y1, (x0 <= x1)%ord -> (y0 <= y1)%ord -> (x0 + y0 <= x1 + y1)%ord.
Proof.
  i.
  etrans.
  - eapply OrdArith.le_add_r; et.
  - eapply OrdArith.le_add_l; et.
Qed.

Lemma mul_le_lt: forall x0 x1 y0 y1, (0 < x1)%ord -> (x0 <= x1)%ord -> (y0 < y1)%ord -> (x0 * y0 < x1 * y1)%ord.
Proof.
  i.
  eapply Ord.le_lt_lt.
  - eapply OrdArith.le_mult_l; et.
  - eapply OrdArith.lt_mult_r; et.
Qed.

Lemma mult_le_le: forall x0 x1 y0 y1, (x0 <= x1)%ord -> (y0 <= y1)%ord -> (x0 * y0 <= x1 * y1)%ord.
Proof.
  i.
  etrans.
  - eapply OrdArith.le_mult_l; et.
  - eapply OrdArith.le_mult_r; et.
Qed.

Lemma expn_pos: forall base o, (1 <= base ^ o)%ord.
Proof. i. rewrite Ord.from_nat_S. eapply Ord.S_supremum. eapply OrdArith.expn_pos. Qed.

Lemma add_one_lt: forall o0 o1, (o0 < o1)%ord -> (o0 + 1 <= o1)%ord.
Proof.
  i.
  rewrite Ord.from_nat_S.
  rewrite OrdArith.add_S.
  rewrite OrdArith.add_O_r.
  eapply Ord.S_supremum; et.
Qed.






Module Type PARAM.
  Parameter c: Ord.t.
  Parameter d: Ord.t.
  Parameter e: Ord.t.
  Parameter f: Ord.t.
End PARAM.

Module Construction (P: PARAM).
  Include P.

  Section CONSTRUCTION.

  Let alpha := (f + 3 + d + e)%ord.
  (* Let alpha_d: ((1 + d) <= alpha)%ord. *)
  (* Proof. unfold alpha. rewrite <- OrdArith.add_O_r at 1. eapply add_le_le; try refl. eapply Ord.O_is_O. Qed. *)
  Let alpha_e: (e <= alpha)%ord.
  Proof.
    unfold alpha.
    eapply OrdArith.add_base_r.
    (* etrans; [eapply OrdArith.add_base_l|]. *)
    (* etrans; [eapply OrdArith.add_base_r|]. *)
    (* rewrite <- OrdArith.add_assoc. rewrite OrdArith.add_assoc. refl. *)
  Qed.

  Let alpha_d: (f + 3 + d <= alpha)%ord.
  Proof.
    unfold alpha.
    eapply OrdArith.add_base_l.
    (* etrans; [eapply OrdArith.add_base_l|]. *)
    (* etrans; [eapply OrdArith.add_base_r|]. *)
    (* rewrite <- OrdArith.add_assoc. *)
    (* eapply add_le_le; try refl. *)
    (* rewrite <- OrdArith.add_assoc. *)
    (* refl. *)
  Qed.

  Definition myF (o0: Ord.t): Ord.t := ((alpha * kappa + c) ^ (o0 + 1))%ord.
  Definition myG (o0 m0: Ord.t): Ord.t := ((alpha * kappa + c) ^ (o0) * alpha * m0)%ord.
  Definition myH (o0: Ord.t): Ord.t := ((alpha * kappa + c) ^ (o0) * 3)%ord.

  (***
                         (myG o0 kappa + d <= myF o0)
  (AM: (m1 < m0)%ord) -> (myG o0 m1 + myH o0 + c <= myG o0 m0)%ord
  (O: (o1 < o0)%ord)  -> (myF o1 + e <= myH o0)%ord
   ***)

  Let NZERO: (Ord.O < alpha * kappa + c)%ord.
  Proof.
    unfold alpha.

    assert(T: (1 < f + 3 + d + e)%ord).
    { assert(U: (1 + 1 <= (Ord.from_nat 3))%ord).
      { rewrite <- OrdArith.add_from_nat. ss. eapply OrdArith.le_from_nat; et. }
      eapply Ord.lt_le_lt; cycle 1.
      { rewrite <- U. refl. }
      rewrite ! OrdArith.add_assoc.
      eapply Ord.lt_le_lt; cycle 1.
      { eapply OrdArith.add_base_r. }
      eapply OrdArith.add_lt_l.
      rewrite Ord.from_nat_S at 1.
      eapply Ord.lt_le_lt.
      { instantiate (1:=1%ord). rewrite Ord.from_nat_S. eapply Ord.S_pos. }
      { rewrite Ord.from_nat_S. eapply OrdArith.add_base_l. }
    }

    eapply Ord.lt_le_lt; cycle 1.
    { eapply OrdArith.add_base_l. }
    rewrite <- OrdArith.mult_1_r.
    eapply Ord.le_lt_lt; cycle 1.
    { instantiate (1:=((f + 3 + d + e) * 1)%ord).
      eapply OrdArith.lt_mult_r.
      - eauto with ord_kappa.
      - rewrite <- T. replace (Ord.from_nat 1) with (Ord.S Ord.O) by ss. eapply Ord.S_pos. }
    eapply mult_le_le.
    - eapply Ord.O_is_O.
    - refl.
  Qed.

  Global Program Instance myG_proper: Proper (Ord.le ==> Ord.le ==> Ord.le) (myG).
  Next Obligation.
    ii. unfold myG.
    rewrite <- H0.
    eapply mult_le_le; et; try refl.
    eapply mult_le_le; et; try refl.
    rewrite <- H. refl.
  Qed.

  Theorem my_thm1: forall o0, (myG o0 kappa + c <= myF o0)%ord.
  Proof.
    i. unfold myF, myG, myH.
    rewrite OrdArith.expn_add; et.
    rewrite OrdArith.expn_1_r; et.
    rewrite OrdArith.mult_dist.
    eapply add_le_le.
    - rewrite <- OrdArith.mult_assoc. refl.
    - rewrite <- (OrdArith.mult_1_l) at 1. eapply mult_le_le; try refl. eapply expn_pos.
    (* OrdArith.add *)
    (* OrdArith.mult *)
    (* OrdArith.expn *)
  Qed.

  Theorem my_thm3
          o0 o1
          (O: (o1 < o0)%ord)
    :
      (myF o1 + e <= myH o0)%ord
  .
  Proof.
    unfold myF, myG, myH.
    eapply add_one_lt in O.
    rewrite <- O.
    rewrite OrdArith.expn_add; et.
    rewrite OrdArith.expn_1_r; et.
    assert(T: (1 + 1 <= 3)%ord).
    { rewrite <- OrdArith.add_from_nat. ss. eapply OrdArith.le_from_nat; et. }
    rewrite <- T.
    rewrite OrdArith.mult_dist with (o2:=1).
    rewrite OrdArith.mult_1_r.
    eapply add_le_le; try refl.
    rewrite <- (OrdArith.mult_1_l) at 1.
    eapply mult_le_le.
    { eapply expn_pos. }
    rewrite <- alpha_e.
    etrans; [|eapply OrdArith.add_base_l].
    rewrite <- (OrdArith.mult_1_r) at 1.
    eapply mult_le_le; try refl.
    eapply Ord.lt_le.
    eauto with ord_kappa.
  Qed.

  Theorem my_thm2
          o0 m0 m1
          (AM: (m1 < m0)%ord)
    :
      (myG o0 m1 + f + myH o0 + d <= myG o0 m0)%ord
  .
  Proof.
    unfold myF, myG, myH.
    eapply add_one_lt in AM.
    rewrite <- AM.
    rewrite OrdArith.mult_dist.
    rewrite OrdArith.mult_1_r.
    rewrite OrdArith.add_assoc.
    rewrite OrdArith.add_assoc.
    eapply add_le_le; try refl.
    rewrite <- alpha_d at 3.
    rewrite OrdArith.mult_dist.
    rewrite OrdArith.mult_dist.
    rewrite <- OrdArith.add_assoc.
    eapply add_le_le; try refl; cycle 1.
    { rewrite <- (OrdArith.mult_1_l) at 1. eapply mult_le_le; try refl. eapply expn_pos. }
    eapply add_le_le; try refl; cycle 1.
    { rewrite <- (OrdArith.mult_1_l) at 1. eapply mult_le_le; try refl. eapply expn_pos. }
  Qed.

  End CONSTRUCTION.

End Construction.


Module MyParam <: PARAM.
  Definition d: Ord.t := 50%ord.
  Definition c: Ord.t := (d + 30)%ord.
  Definition e: Ord.t := 50%ord.
  Definition f: Ord.t := (d + 10)%ord.
End MyParam.

Module C := (Construction MyParam).












(* Lemma upcast_ty: forall T (v: T), Any.ty v↑ = T. admit "ez". Qed. *)
(* Lemma upcast_val: forall T (v: T), Any.val v↑ ~= v. admit "ez". Qed. *)

Lemma pair_downcast_lemma: forall T U (v0 v1: T) a (u: U), (Any.pair v0↑ a)↓ = Some (v1, u) -> v0 = v1 /\ a↓ = Some u.
Proof.
  admit "ez".
Qed.






Inductive opair: Type := mk_opair { ofst: Ord.t; osnd: Ord.t }.
(* Definition opair_lt: opair -> opair -> Prop := fun '(mk_opair x0 x1) '(mk_opair y0 y1) => (x0 < y0)%ord \/ (x0 == y0 /\ x1 < y1)%ord. *)
Inductive opair_lt: opair -> opair -> Prop :=
| intro_opair_lt
    x0 x1 y0 y1
    (LT: (x0 < y0)%ord \/ (x0 == y0 /\ x1 < y1)%ord)
  :
    opair_lt (mk_opair x0 x1) (mk_opair y0 y1)
.
Theorem wf_opair_lt: well_founded opair_lt.
Proof.
  ii. destruct a.
  revert osnd0. pattern ofst0. eapply well_founded_ind. { eapply Ord.lt_well_founded. } clear ofst0. intros ? IH0.
  intro. generalize dependent x. pattern osnd0. eapply well_founded_ind. { eapply Ord.lt_well_founded. } clear osnd0. intros ? IH1.
  econs. i. inv H. des.
  { eapply IH0; et. }
  { eapply IH1; et. i. eapply IH0; et. rewrite <- LT. ss. }
Qed.











Section CANCEL.

  (*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
  Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)



  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.

  Let sk: Sk.t := fold_right Sk.add Sk.unit (List.map SMod.sk mds).
  (* Let skenv: SkEnv.t := Sk.load_skenv sk. *)
  Let mss: list SModSem.t := (List.map ((flip SMod.get_modsem) sk) mds).
  Let sbtb: list (gname * fspecbody) := (List.flat_map (SModSem.fnsems) mss).
  Let stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb.

  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Let mds_mid: list Mod.t := List.map (SMod.to_mid stb) mds.



  Let W: Type := (r_state * p_state).
  (* Let wf: Ord.t -> W -> W -> Prop := top3. *)

  Opaque EventsL.interp_Es.

  Let ms_src: ModSemL.t := ModL.enclose (Mod.add_list mds_src).
  Let ms_mid: ModSemL.t := ModL.enclose (Mod.add_list mds_mid).

  Let p_src := ModSemL.prog ms_src.
  Let p_mid := ModSemL.prog ms_mid.

  Ltac _ord_step := eapply add_le_lt; [refl|eapply OrdArith.lt_from_nat; ss].

  Ltac _step tac :=
    match goal with
    (*** terminal cases ***)
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (triggerUB >>= _) _ ] =>
      unfold triggerUB; mred; _step tac; ss; fail
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (triggerNB >>= _) _ ] =>
      exfalso
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (triggerUB >>= _) ] =>
      exfalso
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (triggerNB >>= _) ] =>
      unfold triggerNB; mred; _step tac; ss; fail

    (*** assume/guarantee ***)
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (assume ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (assume ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar

    (*** default cases ***)
    | _ =>
      (gstep; tac; econs; auto; try (_ord_step);
       (*** some post-processing ***)
       i;
       try match goal with
           | [ |- (eq ==> _)%signature _ _ ] =>
             let v_src := fresh "v_src" in
             let v_tgt := fresh "v_tgt" in
             intros v_src v_tgt ?; subst v_tgt
           end)
    end
  .

  Ltac steps := repeat (mred; try _step ltac:(eapply simg_safe_spec); des_ifs_safe).
  Ltac steps_strong := repeat (mred; try (_step ltac:(idtac)); des_ifs_safe).

  Lemma stb_find_iff fn
    :
      is_some (alist_find fn stb) <-> is_some (find (fun fnsem => dec fn (fst fnsem)) (fnsems ms_mid)).
  Proof.
    admit "in stb <-> in fnsems".
  Qed.

  Let adequacy_type_aux__APC:
    forall at_most o0 mn
           st_src0 st_tgt0
    ,
      simg (fun (st_src1: r_state * p_state * unit) '(st_tgt1, x) => st_tgt1 = st_tgt0)
           (C.myG o0 at_most + C.d)%ord (Ret (st_src0, tt))
           (EventsL.interp_Es p_mid (transl_all mn (interp_hCallE_mid stb (ord_pure o0) (_APC at_most))) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn6_wcompat; eauto with paco. }
    (* induction *)
    intros ? ?. remember (mk_opair o0 at_most) as fuel. move fuel at top. revert at_most o0 Heqfuel.
    pattern fuel. eapply well_founded_induction. { eapply wf_opair_lt. } clear fuel.
    intros fuel IH. i.

    rewrite unfold_APC. destruct st_tgt0 as [rst_tgt0 pst_tgt0]. steps.
    destruct x.
    { steps. }
    steps. destruct (alist_find s stb) eqn:EQ; ss.
    2: { steps. }
    destruct rst_tgt0 as [mrs_tgt0 [|frs_hd frs_tl]]; ss.
    { steps. destruct (Any.downcast t0); steps. }
    steps. destruct (Any.downcast t0); ss.
    2:{ steps. }
    steps. unfold unwrapU. des_ifs; cycle 1.
    { exfalso. hexploit (stb_find_iff s). rewrite EQ. rewrite Heq. clear. intuition. }
    unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
    unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
    rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
    rename Heq0 into INF. rename Heq into IN.
    rename x3 into md0. fold sk in INF. fold sk in INF.
    unfold fun_to_mid.
    steps. assert (f0.(fsb_fspec) = f).
    { admit "fspec table". }
    subst. rewrite Any.upcast_downcast. steps.
    guclo ordC_spec. econs.
    { eapply OrdArith.add_base_l. }
    guclo ordC_spec. econs.
    { eapply C.my_thm2; et. }
    guclo ordC_spec. econs.
    { rewrite OrdArith.add_assoc. refl. }
    rewrite idK_spec at 1.
    guclo bindC_spec. econs.
    { unfold APC. gstep. mred. eapply simg_chooseR; et; [_ord_step|]. i. steps.
      guclo ordC_spec. econs.
      { instantiate (1:=(C.myG x1 x3 + C.d)%ord).
        rewrite <- C.my_thm3; et.
        rewrite <- C.my_thm1; et.
        rewrite OrdArith.add_assoc.
        rewrite OrdArith.add_assoc.
        eapply add_le_le.
        - eapply Ord.lt_le in x4. rewrite <- x4. refl.
        - etrans; [|eapply OrdArith.add_base_l]. etrans; [|eapply OrdArith.add_base_l]. refl.
      }
      eapply IH; auto. econs. left. auto.
    }

    i. ss. destruct vret_tgt as [? []]. destruct vret_src as [? []]. ss. des; subst.
    unfold idK. unfold C.f.
    guclo ordC_spec. econs.
    { rewrite <- OrdArith.add_assoc. refl. }
    steps.
    guclo ordC_spec. econs.
    { eapply OrdArith.add_base_l. }
    { eapply IH; et. econs; et. right; split; et. refl. }
  Qed.

  Let adequacy_type_aux_APC:
    forall o0 st_src0 st_tgt0 mn
    ,
      simg (fun (st_src1: r_state * p_state * unit) '(st_tgt1, _) => st_tgt1 = st_tgt0)
           (C.myF o0)%ord (Ret (st_src0, tt))
           (EventsL.interp_Es p_mid (transl_all mn (interp_hCallE_mid stb (ord_pure o0) APC)) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn6_wcompat; eauto with paco. }
    i. unfold APC.
    guclo ordC_spec. econs.
    { rewrite <- C.my_thm1. refl. }
    unfold C.c.
    guclo ordC_spec. econs.
    { rewrite <- OrdArith.add_assoc. refl. }
    steps.
    guclo ordC_spec. econs.
    { etrans; [|eapply OrdArith.add_base_l]. eapply add_le_le; [|refl].
      instantiate (1:=C.myG o0 x).
      eapply Ord.lt_le in x0. rewrite <- x0. refl. }
    gfinal. right.
    eapply adequacy_type_aux__APC.
  Qed.

  Lemma idK_spec2: forall E A B (a: A) (itr: itree E B), itr = Ret a >>= fun _ => itr. Proof. { i. ired. ss. } Qed.

  Definition formula (o0: ord): Ord.t :=
    match o0 with
    | ord_pure o0 => (10 + C.myF o0)%ord
    | ord_top => 100%ord
    end
  .

  Let wf: W -> W -> Prop := fun '(_, pst_src0) '(_, pst_tgt0) => pst_src0 = pst_tgt0.
  Let wf': forall {X}, (W * X)%type -> (W * X)%type -> Prop := (fun _ '(st_src0, rv_src) '(st_tgt0, rv_tgt) => wf st_src0 st_tgt0 /\ rv_src = rv_tgt).

  Ltac resub :=
    repeat multimatch goal with
           | |- context[ITree.trigger ?e] =>
             match e with
             | subevent _ _ => idtac
             | _ => replace (ITree.trigger e) with (trigger e) by refl
             end
           | |- context[@subevent _ ?F ?prf _ (?e|)%sum] => replace (@subevent _ F prf _ (e|)%sum) with (@subevent _ F _ _ e) by refl
           | |- context[@subevent _ ?F ?prf _ (|?e)%sum] => replace (@subevent _ F prf _ (|e)%sum) with (@subevent _ F _ _ e) by refl
           end.

  Let adequacy_type_aux:
    forall
      o0
      A (body: itree _ A) st_src0 st_tgt0 mn
      (SIM: wf st_src0 st_tgt0)
    ,
      simg wf'
           (formula o0 + 50)%ord
           (EventsL.interp_Es p_src (transl_all mn (interp_hCallE_src body)) st_src0)
           (EventsL.interp_Es p_mid (transl_all mn (interp_hCallE_mid stb o0 body)) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn6_wcompat; eauto with paco. }
    gcofix CIH. i. ides body.
    { steps. }
    { steps. gbase. eapply CIH; ss. }

    destruct e; cycle 1.
    { rewrite <- bind_trigger. resub. steps.
      destruct s; ss.
      { destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
        destruct p; ss.
        - steps. gbase. eapply CIH; ss; et.
        - steps. gbase. eapply CIH; ss; et.
      }
      { dependent destruction e.
        - steps_strong. exists x_tgt. steps. gbase. eapply CIH; et.
        - steps_strong. exists x_src. steps. gbase. eapply CIH; et.
        - steps_strong. gbase. eapply CIH; et.
      }
    }
    dependent destruction h.
    rewrite <- bind_trigger. resub.
    destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
    ired_both. destruct tbr.
    (*
PURE *)
    { seal_left. steps. destruct (alist_find fn stb) eqn:EQ.
      2: { steps. }
      steps. destruct (Any.downcast varg_src).
      2: { steps. }
      Local Opaque ord_lt. steps.
      destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]]; ss.
      { steps. }
      unseal_left. steps.
      unfold unwrapU. des_ifs; cycle 1.
      { exfalso. hexploit (stb_find_iff fn). rewrite EQ. rewrite Heq. clear. intuition. }
      steps.

      unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
      unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
      rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
      rename Heq0 into INF. rename Heq into IN.
      rename x0 into md0. fold sk in INF. fold sk in INF.
      unfold fun_to_mid. ss.
      assert (f = f0).
      { admit "uniqueness". }
      subst. rewrite Any.upcast_downcast. steps.
      guclo ordC_spec. econs.
      { eapply OrdArith.add_base_l. }

      rewrite idK_spec2 at 1.
      guclo bindC_spec. econs.
      { gfinal. right. eapply paco6_mon. { eapply adequacy_type_aux_APC. } ii; ss. }
      i. steps. steps_strong. exists (Any.upcast x0). steps.
      gbase. eapply CIH. ss.
    }

    (* IMPURE *)
    { seal_left. steps. destruct (alist_find fn stb) eqn:EQ.
      2: { steps. }
      steps. destruct (Any.downcast varg_src).
      2: { steps. }
      Local Opaque ord_lt. steps.
      destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]]; ss.
      { steps. }
      unseal_left. steps.
      unfold unwrapU. des_ifs; cycle 1.
      { exfalso. hexploit (stb_find_iff fn). rewrite EQ. rewrite Heq. clear. intuition. }
      steps.

      unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
      unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
      rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
      rename Heq0 into INF. rename Heq into IN.
      rename x0 into md0. fold sk in INF. fold sk in INF.
      unfold fun_to_mid. ss.
      assert (f = f0).
      { admit "uniqueness". }
      subst. rewrite Any.upcast_downcast. steps.
      guclo ordC_spec. econs.
      { eapply OrdArith.add_base_l. }

      rewrite idK_spec2 at 1.
      guclo bindC_spec. econs.
      { gfinal. right. eapply paco6_mon. { eapply adequacy_type_aux_APC. } ii; ss. }
      i. steps. steps_strong. exists (Any.upcast x0). steps.
      gbase. eapply CIH. ss.
    }


    }
      { eapply OrdArith.add_base_l. instantiate (2:=formula o0). instantiate (1:=(100+C.myF x)%ord).
        eapply OrdArith.add_base_l.


        refl.


      { instantiate (1:=_ + _). admit "". }
      rewrite idK_spec2 at 1.
      guclo bindC_spec. econs.
      { gfinal. right. eapply paco6_mon. { eapply adequacy_type_aux_APC. } ii; ss. }
      i. steps. steps_strong. exists (Any.upcast x0). steps.
      gbase. eapply CIH. ss.
    }

      econs.
      specialize (CIH0 o0 _ (k (Any.upcast x0)) (rst_src0, pst_tgt0) (mrs_tgt0, frs_tgt_hd :: frs_tgt_tl, pst_tgt0)).
      instantiate (1:=Any.upcast x0).


      eapply CIH0.

      n

      eapply adequacy_type_aux_APC.


        unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
        unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
        rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
        rename Heq0 into INF. rename Heq into IN.
        rename x0 into md0. fold sk in INF. fold sk in INF.

        unfold ms_src, mds_src, SMod.to_src in Heq0. rewrite SMod.transl_fnsems in Heq0.
        unfold SMod.load_fnsems in Heq0. apply find_some in Heq0. des; ss. des_sumbool; subst.
        rewrite in_flat_map in Heq0. des; ss. rewrite in_flat_map in Heq1. des; ss. des_ifs. ss; des; ss; clarify.
        rename Heq1 into INF0. rename Heq0 into IN0.
        rename x0 into md1. fold sk in INF0. fold sk in INF0.




  Let adequacy_type_aux:
    forall
      AA AR
      (args: AA)
      o0
      body st_src0 st_tgt0 mn
      (SIM: wf st_src0 st_tgt0)
    ,
      simg wf'
           (formula o0 + 10)%ord
           (EventsL.interp_Es p_src (transl_all mn (if is_pure o0 then trigger (Choose _) else ((fun_to_src (AA:=AA) (AR:=AR) body) args↑))) st_src0)
           (EventsL.interp_Es p_mid (transl_all mn ((fun_to_mid stb body) (o0, args)↑)) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn6_wcompat; eauto with paco. }
    gcofix CIH. i.
    unfold fun_to_src, fun_to_mid. steps.
    rewrite Any.upcast_downcast. steps.
    unfold body_to_src, cfun. rewrite Any.upcast_downcast. ss. steps.
    destruct o0; ss.
    - (*** PURE ***)
      seal_left.
      steps.
      unseal_left.
      erewrite idK_spec2 at 1.
      guclo ordC_spec. econs.
      { eapply OrdArith.add_base_l. }
      guclo bindC_spec.
      econs.
      { gfinal. right. eapply paco6_mon. { eapply adequacy_type_aux_APC. } ii; ss. }
      ii; ss. des_ifs. des_u.
      steps_strong. esplits; eauto. steps.
    - (*** IMPURE ***)
      steps. unfold body_to_mid.
      abstr (body args) itr. clear body args AA.

      guclo ordC_spec. econs.
      { instantiate (1:=(10 + 100)%ord). rewrite <- ! OrdArith.add_from_nat. ss. refl. }
      (* { instantiate (1:=(1 + 99)%ord). rewrite <- OrdArith.add_from_nat. ss. refl. } *)
      guclo bindC_spec. eapply bindR_intro with (RR:=wf'); cycle 1.
      { ii. subst. des_ifs. steps. r in SIM0. des; subst; ss. }

      revert_until CIH. gcofix CIH0. i.

      ides itr.
      { steps. }
      { steps. gbase. eapply CIH0; ss. }
      destruct e; cycle 1.
      {
        rewrite <- bind_trigger. resub. steps.
        destruct s; ss.
        {
          destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
          destruct p; ss.
          - steps. instantiate (1:=100). gbase. eapply CIH0; ss; et.
          - steps. instantiate (1:=100). gbase. eapply CIH0; ss; et.
        }
        { dependent destruction e.
          - steps_strong. unshelve esplits; et. instantiate (1:=100). steps. gbase. eapply CIH0; ss; et.
          - steps_strong. unshelve esplits; et. instantiate (1:=100). steps. gbase. eapply CIH0; ss; et.
          - steps_strong. unshelve esplits; et. instantiate (1:=100). steps. gbase. eapply CIH0; ss; et.
        }
      }
      dependent destruction h.
      rewrite <- bind_trigger. resub.
      Opaque fun_to_src fun_to_mid.

      destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
      ired_both.
      destruct tbr.
      + (*** PURE CALL ***)
        mred. steps.

        (* seal_left. *)
        (* Ltac step := (mred; try _step; des_ifs_safe). *)
        (* step; try by eapply OrdArith.lt_from_nat. *)
        (* step; try by eapply OrdArith.lt_from_nat. *)
        (* unseal_left. *)
        (* steps_strong. *)
        (* set ((120 + formula (ord_pure x) + 100)%ord). *)
        (* instantiate (1:=(120 + formula (ord_pure x) + 100)%ord). *)
        (* seal_left. *)

        destruct (alist_find fn stb) eqn:EQ.
        2:{ steps. }
        steps.
        destruct (Any.downcast varg_src) eqn:ARG.
        2:{ steps. }
        steps.
        destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]]; ss.
        { steps. }
        steps.
        unfold unwrapU. des_ifs; cycle 1.
        { admit "". }
        steps_strong. eexists. steps.
        unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
        unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
        rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
        rename Heq0 into INF. rename Heq into IN.
        rename x1 into md0. fold sk in INF. fold sk in INF.
        mred.
        guclo ordC_spec. econs.
        {

          admit "".
          (* instantiate (1:=(120 + (10 + C.myF x + 10))%ord). *)
          (* rewrite <- ! OrdArith.add_assoc. eapply add_le_le; try refl. eapply OrdArith.le_from_nat; ss. lia. *)

        }
        rename x into o1.
        rewrite <- bind_bind.
        rewrite <- bind_bind.
        guclo bindC_spec. econs.
        * (* guclo ordC_spec. econs. *)
          (* { eapply OrdArith.add_base_r. } *)
          (* gbase. eapply CIH; et. *)
          gbase. hexploit CIH; et.
          { instantiate (1:=(mrs_tgt0, ε :: frs_tgt_hd :: frs_tgt_tl, pst_tgt0)). instantiate (1:= (rst_src0, pst_tgt0)). ss. }
          intro T. instantiate (2:=(ord_pure o1)) in T. ss.
          mred.
          (*** applying reduction in "T" begin ***)
          (*** TODO: make prw "in" tactic ***)
          revert T. pose (fun (x: Prop) (y: Prop) => (x -> y)) as myf.
          match goal with | |- ?a -> ?b => replace (a -> b) with (myf a b) by refl end.
          try Red.prw ltac:(IRed._red_gen) 2 2 0.
          subst myf; cbn. intro T.
          (*** applying reduction in "T" end ***)
          eapply T.
        * ii. des_ifs. destruct p, p0; ss. des; subst.
          step; try by eapply OrdArith.lt_from_nat. steps.
          destruct r1; ss.
          des_ifs.
          { unfold triggerNB. steps; try by eapply OrdArith.lt_from_nat. (*** TODO: fix tactic, don't unfold triggerNB ***) }
          repeat (step; try by eapply OrdArith.lt_from_nat).
          guclo ordC_spec. econs.
          { instantiate (1:=100%ord). eapply OrdArith.le_from_nat; ss. lia. }
          gbase. eapply CIH0. ss.
      + (*** IMPURE CALL ***)
        mred.
        destruct rst_src0 as [mrs_src0 [|frs_src_hd frs_src_tl]]; ss.
        { admit "SOMEHOW". }
        mred. steps. instantiate (2:=(100 + (100 + 10) + 42)%ord). instantiate (1:=0%ord).
        guclo ordC_spec. econs. { rewrite OrdArith.add_O_r. refl. }
        destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]]; ss.
        { steps. }
        steps. unfold unwrapU at 2. des_ifs; cycle 1.
        { admit "unwrapN!!!!!!!!!!!!!!!!!!". }
        steps.
        unfold unwrapU. des_ifs; cycle 1.
        { steps. }
        steps.

        unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
        unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
        rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq1. des; ss. des_ifs. ss; des; ss; clarify.
        rename Heq1 into INF. rename Heq into IN.
        rename x0 into md0. fold sk in INF. fold sk in INF.

        unfold ms_src, mds_src, SMod.to_src in Heq0. rewrite SMod.transl_fnsems in Heq0.
        unfold SMod.load_fnsems in Heq0. apply find_some in Heq0. des; ss. des_sumbool; subst.
        rewrite in_flat_map in Heq0. des; ss. rewrite in_flat_map in Heq1. des; ss. des_ifs. ss; des; ss; clarify.
        rename Heq1 into INF0. rename Heq0 into IN0.
        rename x0 into md1. fold sk in INF0. fold sk in INF0.

        assert(md0 = md1); subst.
        { admit "ez - uniqueness". }

        assert(f = f0); subst.
        { admit "ez - uniqueness". }

        guclo ordC_spec. econs.
        { eapply OrdArith.add_base_l. }
        guclo bindC_spec.
        econs.
        * hexploit CIH; et; cycle 1.
          { intro T. gbase. instantiate (3:=ord_top) in T. ss. eapply T. }
          { ss. }
        * ii; ss. des_ifs. steps. destruct p, p0; ss. des; subst.
          steps. destruct r1; ss. des_ifs.
          { unfold triggerNB. (step; try by eapply OrdArith.lt_from_nat). (*** TODO: fix tactic ***) }
          destruct r0; ss. des_ifs. { admit "somehow". } steps.
          instantiate (1:=100).
          gbase. eapply CIH0 ;ss.
  Unshelve.
    all: try (by econs; et).
    all: try (by exact Ord.O).
    all: ss.
  Unshelve.
    all: try (by exact unit).
  Qed.

  Theorem adequacy_type_m2s: Beh.of_program (ModL.compile (Mod.add_list mds_mid)) <1=
                             Beh.of_program (ModL.compile (Mod.add_list mds_src)).
  Proof.
    eapply adequacy_global.
    exists (100)%ord. ss.
    ginit.
    { eapply cpn5_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr. Local Opaque ModSemL.prog. ss.
    unfold ITree.map.
    unfold assume.
    steps.
    instantiate (1:=(10 + (100 + 10) + 42)%ord).
    esplits; et. { admit "ez - wf". } steps.
    Local Transparent ModSemL.prog.
    unfold ModSemL.prog at 4.
    unfold ModSemL.prog at 2.
    Local Opaque ModSemL.prog.
    ss. steps.
    (* Opaque ModSemL.initial_r_state. *)
    (* Opaque ModSemL.initial_p_state. *)
    fold ms_src. fold ms_mid.
    set (rs_src0 := initial_r_state ms_src) in *.
    set (rs_tgt0 := initial_r_state ms_mid) in *.
    assert(exists mrs_src0 hd_src tl_src, rs_src0 = (mrs_src0, hd_src :: tl_src)).
    { esplits. refl. }
    assert(exists mrs_tgt0 hd_tgt tl_tgt, rs_tgt0 = (mrs_tgt0, hd_tgt :: tl_tgt)).
    { esplits. refl. }
    des. clearbody rs_src0 rs_tgt0. subst.
    unfold unwrapU at 1. des_ifs; cycle 1.
    { steps. }
    unfold unwrapU. des_ifs; cycle 1.
    { admit "unwrapN!!!!!!!!!!". }


    unfold ms_mid, mds_mid, SMod.to_mid in Heq0. rewrite SMod.transl_fnsems in Heq0.
    unfold SMod.load_fnsems in Heq0. apply find_some in Heq0. des; ss. des_sumbool; subst.
    rewrite in_flat_map in Heq0. des; ss. rewrite in_flat_map in Heq2. des; ss. des_ifs. ss; des; ss; clarify. ss. subst.
    rename Heq2 into INF. rename Heq0 into IN.
    rename x into md0. fold sk in INF. fold sk in INF.

    unfold ms_src, mds_src, SMod.to_src in Heq. rewrite SMod.transl_fnsems in Heq.
    unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. destruct p; ss. des_sumbool; subst.
    rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
    rename Heq0 into INF0. rename Heq into IN0.
    rename x into md1. fold sk in INF0. fold sk in INF0.

    assert(md0 = md1); subst.
    { admit "ez - uniqueness". }
    assert(f = f0).
    { admit "ez - uniqueness". }
    subst.
    fold ms_src. fold ms_mid. fold p_src. fold p_mid.

    steps.

    match goal with
    | [ |- gpaco5 _ _ _ _ _ _ _ ?i_src _ ] => remember i_src as tmp
    end.
    replace (([]: list val)↑) with (Any.pair ord_top↑ ([]: list val)↑) by admit "TODO".
    subst tmp.

    guclo ordC_spec. econs.
    { eapply OrdArith.add_base_l. }
    guclo bindC_spec.
    econs.
    - hexploit adequacy_type_aux; cycle 1.
      { intro T. gfinal. right. instantiate (3:=ord_top) in T. ss. eapply T. }
      ss. unfold ms_src, ms_mid. unfold initial_p_state.
      apply func_ext. intro mn. unfold mds_src, mds_mid, SMod.to_src, SMod.to_mid.
      rewrite ! SMod.transl_initial_mrs. ss.
    - ii. rr in SIM. des_ifs. des; ss. subst. r in SIM. des_ifs. steps.
  Unshelve.
    all: ss.
    all: try (by exact Ord.O).
    all: try (by econs; et).
  Qed.

  (*** TODO: remove redundancy with Hoareproof0 ***)
  Ltac resub :=
    repeat multimatch goal with
           | |- context[ITree.trigger ?e] =>
             match e with
             | subevent _ _ => idtac
             | _ => replace (ITree.trigger e) with (trigger e) by refl
             end
           | |- context[@subevent _ ?F ?prf _ (?e|)%sum] => replace (@subevent _ F prf _ (e|)%sum) with (@subevent _ F _ _ e) by refl
           | |- context[@subevent _ ?F ?prf _ (|?e)%sum] => replace (@subevent _ F prf _ (|e)%sum) with (@subevent _ F _ _ e) by refl
           end.

  Let adequacy_type_aux:
    forall
      o0
      A (body: itree _ A) st_src0 st_tgt0 mn
      (SIM: wf st_src0 st_tgt0)
    ,
      simg wf'
           100%ord
           (EventsL.interp_Es p_src (transl_all mn (interp_hCallE_src body)) st_src0)
           (EventsL.interp_Es p_mid (transl_all mn (interp_hCallE_mid stb o0 body)) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
    gcofix CIH. i. ides body.
    { steps. }
    { steps. gbase. eapply CIH; ss. }

    destruct e; cycle 1.
    { rewrite <- bind_trigger. resub. steps.
      destruct s; ss.
      { destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
        destruct p; ss.
        - steps. gbase. eapply CIH; ss; et.
        - steps. gbase. eapply CIH; ss; et.
      }
      { dependent destruction e.
        - steps_strong. exists x_tgt. steps. gbase. eapply CIH; et.
        - steps_strong. exists x_src. steps. gbase. eapply CIH; et.
        - steps_strong. gbase. eapply CIH; et.
      }
    }
    dependent destruction h.
    rewrite <- bind_trigger. resub.
    destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
    ired_both. destruct tbr.
    (* PURE *)
    { steps_strong.
      { admit "". }
      eexists. steps. destruct (alist_find fn stb) eqn:EQ.
      2: { steps. }
      steps. destruct (Any.downcast varg_src).
      2: { steps. }
      steps. destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]]; ss.
      { steps. }
      steps. clear x0. unfold unwrapU. des_ifs; cycle 1.
      { exfalso. hexploit (stb_find_iff fn). rewrite EQ. rewrite Heq. clear. intuition. }
      steps.

      guclo ordC_spec. econs.
      { instantiate (1:=_ + _). admit "". }
      rewrite idK_spec2 at 1.
      guclo bindC_spec. econs.
      {


  Let adequacy_type_aux:
    forall
      AA AR
      args
      o0
      body st_src0 st_tgt0 mn
      (SIM: wf st_src0 st_tgt0)
    ,
      simg wf'
           (formula o0 + 10)%ord
           (* (if is_pure o0 then trigger (Choose _) else (interp_Es p_src ((fun_to_src (AA:=AA) (AR:=AR) body) args↑) st0)) *)
           (EventsL.interp_Es p_src (transl_all mn (if is_pure o0 then trigger (Choose _) else ((fun_to_src (AA:=AA) (AR:=AR) body) args))) st_src0)
           (EventsL.interp_Es p_mid (transl_all mn ((fun_to_mid stb body) (Any.pair o0↑ args))) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
    gcofix CIH. i.
    unfold fun_to_src, fun_to_mid. steps. unfold unwrapN.
    destruct (Any.downcast (Any.pair (Any.upcast o0) args)) eqn:T; cycle 1.
    { steps. }
    destruct p.
    eapply pair_downcast_lemma in T. des; subst; ss. eapply Any.downcast_upcast in T0. des; subst.
    unfold body_to_src, cfun. steps. rewrite Any.upcast_downcast. ss. steps.
    destruct o; ss.
    - (*** PURE ***)
      seal_left.
      steps.
      unseal_left.
      erewrite idK_spec2 at 1.
      guclo ordC_spec. econs.
      { eapply OrdArith.add_base_l. }
      guclo bindC_spec.
      econs.
      { gfinal. right. eapply paco5_mon. { eapply adequacy_type_aux_APC. } ii; ss. }
      ii; ss. des_ifs. des_u.
      steps_strong. eexists. steps.
    -

      { admit "". }
      esplits; eauto.

      ste
 steps.
    - (*** IMPURE ***)
      steps. unfold body_to_mid.
      abstr (body a) itr. clear body a AA.

      guclo ordC_spec. econs.
      { instantiate (1:=(10 + 100)%ord). rewrite <- ! OrdArith.add_from_nat. ss. refl. }
      (* { instantiate (1:=(1 + 99)%ord). rewrite <- OrdArith.add_from_nat. ss. refl. } *)
      guclo bindC_spec. eapply bindR_intro with (RR:=wf'); cycle 1.
      { ii. subst. des_ifs. steps. r in SIM0. des; subst; ss. }

      revert_until CIH. gcofix CIH0. i.

      ides itr.
      { steps. }
      { steps. gbase. eapply CIH0; ss. }
      destruct e; cycle 1.
      {

        (*** TODO: remove redundancy with Hoareproof0 ***)
  Ltac resub :=
    repeat multimatch goal with
           | |- context[ITree.trigger ?e] =>
             match e with
             | subevent _ _ => idtac
             | _ => replace (ITree.trigger e) with (trigger e) by refl
             end
           | |- context[@subevent _ ?F ?prf _ (?e|)%sum] => replace (@subevent _ F prf _ (e|)%sum) with (@subevent _ F _ _ e) by refl
           | |- context[@subevent _ ?F ?prf _ (|?e)%sum] => replace (@subevent _ F prf _ (|e)%sum) with (@subevent _ F _ _ e) by refl
           end.
        rewrite <- bind_trigger. resub. steps.
        destruct s; ss.
        {
          destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
          destruct p; ss.
          - steps. instantiate (1:=100). gbase. eapply CIH0; ss; et.
          - steps. instantiate (1:=100). gbase. eapply CIH0; ss; et.
        }
        { dependent destruction e.
          - steps. unshelve esplits; et. instantiate (1:=100). steps. gbase. eapply CIH0; ss; et.
          - steps. unshelve esplits; et. instantiate (1:=100). steps. gbase. eapply CIH0; ss; et.
          - steps. unshelve esplits; et. instantiate (1:=100). steps. gbase. eapply CIH0; ss; et.
        }
      }
      dependent destruction h.
      rewrite <- bind_trigger. resub.
      Opaque fun_to_src fun_to_mid.

      destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
      ired_both.
      destruct tbr.
      + (*** PURE CALL ***)
        mred.
        seal_left.
        Ltac step := (mred; try _step; des_ifs_safe).
        step; try by eapply OrdArith.lt_from_nat.
        step; try by eapply OrdArith.lt_from_nat.
        unseal_left.
        step; try by eapply OrdArith.lt_from_nat.
        instantiate (1:=(120 + formula (ord_pure x) + 100)%ord).
        seal_left.

        steps.
        destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]]; ss.
        { unseal_left. steps. }
        steps.
        unfold unwrapU. des_ifs; cycle 1.
        { admit "unwrapN!!!!!!!!!!!!!!!!!!!!!!!!!!". }
        steps.
        unseal_left.
        unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
        unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
        rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
        rename Heq0 into INF. rename Heq into IN.
        rename x1 into md0. fold sk in INF. fold sk in INF.
        mred.
        guclo ordC_spec. econs.
        { instantiate (1:=(120 + (10 + C.myF x + 10))%ord).
          rewrite <- ! OrdArith.add_assoc. eapply add_le_le; try refl. eapply OrdArith.le_from_nat; ss. lia. }
        rename x into o1.
        rewrite <- bind_bind.
        rewrite <- bind_bind.
        guclo bindC_spec. econs.
        * (* guclo ordC_spec. econs. *)
          (* { eapply OrdArith.add_base_r. } *)
          (* gbase. eapply CIH; et. *)
          gbase. hexploit CIH; et.
          { instantiate (1:=(mrs_tgt0, ε :: frs_tgt_hd :: frs_tgt_tl, pst_tgt0)). instantiate (1:= (rst_src0, pst_tgt0)). ss. }
          intro T. instantiate (2:=(ord_pure o1)) in T. ss.
          mred.
          (*** applying reduction in "T" begin ***)
          (*** TODO: make prw "in" tactic ***)
          revert T. pose (fun (x: Prop) (y: Prop) => (x -> y)) as myf.
          match goal with | |- ?a -> ?b => replace (a -> b) with (myf a b) by refl end.
          try Red.prw ltac:(IRed._red_gen) 2 2 0.
          subst myf; cbn. intro T.
          (*** applying reduction in "T" end ***)
          eapply T.
        * ii. des_ifs. destruct p, p0; ss. des; subst.
          step; try by eapply OrdArith.lt_from_nat. steps.
          destruct r1; ss.
          des_ifs.
          { unfold triggerNB. steps; try by eapply OrdArith.lt_from_nat. (*** TODO: fix tactic, don't unfold triggerNB ***) }
          repeat (step; try by eapply OrdArith.lt_from_nat).
          guclo ordC_spec. econs.
          { instantiate (1:=100%ord). eapply OrdArith.le_from_nat; ss. lia. }
          gbase. eapply CIH0. ss.
      + (*** IMPURE CALL ***)
        mred.
        destruct rst_src0 as [mrs_src0 [|frs_src_hd frs_src_tl]]; ss.
        { admit "SOMEHOW". }
        mred. steps. instantiate (2:=(100 + (100 + 10) + 42)%ord). instantiate (1:=0%ord).
        guclo ordC_spec. econs. { rewrite OrdArith.add_O_r. refl. }
        destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]]; ss.
        { steps. }
        steps. unfold unwrapU at 2. des_ifs; cycle 1.
        { admit "unwrapN!!!!!!!!!!!!!!!!!!". }
        steps.
        unfold unwrapU. des_ifs; cycle 1.
        { steps. }
        steps.

        unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
        unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
        rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq1. des; ss. des_ifs. ss; des; ss; clarify.
        rename Heq1 into INF. rename Heq into IN.
        rename x0 into md0. fold sk in INF. fold sk in INF.

        unfold ms_src, mds_src, SMod.to_src in Heq0. rewrite SMod.transl_fnsems in Heq0.
        unfold SMod.load_fnsems in Heq0. apply find_some in Heq0. des; ss. des_sumbool; subst.
        rewrite in_flat_map in Heq0. des; ss. rewrite in_flat_map in Heq1. des; ss. des_ifs. ss; des; ss; clarify.
        rename Heq1 into INF0. rename Heq0 into IN0.
        rename x0 into md1. fold sk in INF0. fold sk in INF0.

        assert(md0 = md1); subst.
        { admit "ez - uniqueness". }

        assert(f = f0); subst.
        { admit "ez - uniqueness". }

        guclo ordC_spec. econs.
        { eapply OrdArith.add_base_l. }
        guclo bindC_spec.
        econs.
        * hexploit CIH; et; cycle 1.
          { intro T. gbase. instantiate (3:=ord_top) in T. ss. eapply T. }
          { ss. }
        * ii; ss. des_ifs. steps. destruct p, p0; ss. des; subst.
          steps. destruct r1; ss. des_ifs.
          { unfold triggerNB. (step; try by eapply OrdArith.lt_from_nat). (*** TODO: fix tactic ***) }
          destruct r0; ss. des_ifs. { admit "somehow". } steps.
          instantiate (1:=100).
          gbase. eapply CIH0 ;ss.
  Unshelve.
    all: try (by econs; et).
    all: try (by exact Ord.O).
    all: ss.
  Unshelve.
    all: try (by exact unit).
  Qed.

  Theorem adequacy_type_m2s: Beh.of_program (ModL.compile (Mod.add_list mds_mid)) <1=
                             Beh.of_program (ModL.compile (Mod.add_list mds_src)).
  Proof.
    eapply adequacy_global.
    exists (100)%ord. ss.
    ginit.
    { eapply cpn5_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr. Local Opaque ModSemL.prog. ss.
    unfold ITree.map.
    unfold assume.
    steps.
    instantiate (1:=(10 + (100 + 10) + 42)%ord).
    esplits; et. { admit "ez - wf". } steps.
    Local Transparent ModSemL.prog.
    unfold ModSemL.prog at 4.
    unfold ModSemL.prog at 2.
    Local Opaque ModSemL.prog.
    ss. steps.
    (* Opaque ModSemL.initial_r_state. *)
    (* Opaque ModSemL.initial_p_state. *)
    fold ms_src. fold ms_mid.
    set (rs_src0 := initial_r_state ms_src) in *.
    set (rs_tgt0 := initial_r_state ms_mid) in *.
    assert(exists mrs_src0 hd_src tl_src, rs_src0 = (mrs_src0, hd_src :: tl_src)).
    { esplits. refl. }
    assert(exists mrs_tgt0 hd_tgt tl_tgt, rs_tgt0 = (mrs_tgt0, hd_tgt :: tl_tgt)).
    { esplits. refl. }
    des. clearbody rs_src0 rs_tgt0. subst.
    unfold unwrapU at 1. des_ifs; cycle 1.
    { steps. }
    unfold unwrapU. des_ifs; cycle 1.
    { admit "unwrapN!!!!!!!!!!". }


    unfold ms_mid, mds_mid, SMod.to_mid in Heq0. rewrite SMod.transl_fnsems in Heq0.
    unfold SMod.load_fnsems in Heq0. apply find_some in Heq0. des; ss. des_sumbool; subst.
    rewrite in_flat_map in Heq0. des; ss. rewrite in_flat_map in Heq2. des; ss. des_ifs. ss; des; ss; clarify. ss. subst.
    rename Heq2 into INF. rename Heq0 into IN.
    rename x into md0. fold sk in INF. fold sk in INF.

    unfold ms_src, mds_src, SMod.to_src in Heq. rewrite SMod.transl_fnsems in Heq.
    unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. destruct p; ss. des_sumbool; subst.
    rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
    rename Heq0 into INF0. rename Heq into IN0.
    rename x into md1. fold sk in INF0. fold sk in INF0.

    assert(md0 = md1); subst.
    { admit "ez - uniqueness". }
    assert(f = f0).
    { admit "ez - uniqueness". }
    subst.
    fold ms_src. fold ms_mid. fold p_src. fold p_mid.

    steps.

    match goal with
    | [ |- gpaco6 _ _ _ _ _ _ _ _ ?i_src _ ] => remember i_src as tmp
    end.
    replace (([]: list val)↑) with (Any.pair ord_top↑ ([]: list val)↑) by admit "TODO".
    subst tmp.

    guclo ordC_spec. econs.
    { eapply OrdArith.add_base_l. }
    guclo bindC_spec.
    econs.
    - hexploit adequacy_type_aux; cycle 1.
      { intro T. gfinal. right. instantiate (3:=ord_top) in T. ss. eapply T. }
      ss. unfold ms_src, ms_mid. unfold initial_p_state.
      apply func_ext. intro mn. unfold mds_src, mds_mid, SMod.to_src, SMod.to_mid.
      rewrite ! SMod.transl_initial_mrs. ss.
    - ii. rr in SIM. des_ifs. des; ss. subst. r in SIM. des_ifs. steps.
  Unshelve.
    all: ss.
    all: try (by exact Ord.O).
    all: try (by econs; et).
  Qed.

End CANCEL.

Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Import ModSemL.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef.
Require Import SimSTS.
Require Import SimGlobal.
Require Import HoareDef.
From Ordinal Require Import Ordinal Arithmetic.

Set Implicit Arguments.

































Lemma add_le_lt: forall x0 x1 y0 y1, (x0 <= x1)%ord -> (y0 < y1)%ord -> (x0 + y0 < x1 + y1)%ord.
Proof.
  i.
  eapply Ord.le_lt_lt.
  - eapply OrdArith.le_add_l; et.
  - eapply OrdArith.lt_add_r; et.
Qed.

Lemma add_le_le: forall x0 x1 y0 y1, (x0 <= x1)%ord -> (y0 <= y1)%ord -> (x0 + y0 <= x1 + y1)%ord.
Proof.
  i.
  etrans.
  - eapply OrdArith.le_add_r; et.
  - eapply OrdArith.le_add_l; et.
Qed.

Lemma mul_le_lt: forall x0 x1 y0 y1, (0 < x1)%ord -> (x0 <= x1)%ord -> (y0 < y1)%ord -> (x0 * y0 < x1 * y1)%ord.
Proof.
  i.
  eapply Ord.le_lt_lt.
  - eapply OrdArith.le_mult_l; et.
  - eapply OrdArith.lt_mult_r; et.
Qed.

Lemma mult_le_le: forall x0 x1 y0 y1, (x0 <= x1)%ord -> (y0 <= y1)%ord -> (x0 * y0 <= x1 * y1)%ord.
Proof.
  i.
  etrans.
  - eapply OrdArith.le_mult_l; et.
  - eapply OrdArith.le_mult_r; et.
Qed.

Lemma expn_pos: forall base o, (1 <= base ^ o)%ord.
Proof. i. rewrite Ord.from_nat_S. eapply Ord.S_supremum. eapply OrdArith.expn_pos. Qed.

Lemma add_one_lt: forall o0 o1, (o0 < o1)%ord -> (o0 + 1 <= o1)%ord.
Proof.
  i.
  rewrite Ord.from_nat_S.
  rewrite OrdArith.add_S.
  rewrite OrdArith.add_O_r.
  eapply Ord.S_supremum; et.
Qed.






Module Type PARAM.
  Parameter c: Ord.t.
  Parameter d: Ord.t.
  Parameter e: Ord.t.
  Parameter f: Ord.t.
End PARAM.

Module Construction (P: PARAM).
  Include P.

  Section CONSTRUCTION.

  Let alpha := (f + 3 + d + e)%ord.
  (* Let alpha_d: ((1 + d) <= alpha)%ord. *)
  (* Proof. unfold alpha. rewrite <- OrdArith.add_O_r at 1. eapply add_le_le; try refl. eapply Ord.O_is_O. Qed. *)
  Let alpha_e: (e <= alpha)%ord.
  Proof.
    unfold alpha.
    eapply OrdArith.add_base_r.
    (* etrans; [eapply OrdArith.add_base_l|]. *)
    (* etrans; [eapply OrdArith.add_base_r|]. *)
    (* rewrite <- OrdArith.add_assoc. rewrite OrdArith.add_assoc. refl. *)
  Qed.

  Let alpha_d: (f + 3 + d <= alpha)%ord.
  Proof.
    unfold alpha.
    eapply OrdArith.add_base_l.
    (* etrans; [eapply OrdArith.add_base_l|]. *)
    (* etrans; [eapply OrdArith.add_base_r|]. *)
    (* rewrite <- OrdArith.add_assoc. *)
    (* eapply add_le_le; try refl. *)
    (* rewrite <- OrdArith.add_assoc. *)
    (* refl. *)
  Qed.

  Definition myF (o0: Ord.t): Ord.t := ((alpha * kappa + c) ^ (o0 + 1))%ord.
  Definition myG (o0 m0: Ord.t): Ord.t := ((alpha * kappa + c) ^ (o0) * alpha * m0)%ord.
  Definition myH (o0: Ord.t): Ord.t := ((alpha * kappa + c) ^ (o0) * 3)%ord.

  (***
                         (myG o0 kappa + d <= myF o0)
  (AM: (m1 < m0)%ord) -> (myG o0 m1 + myH o0 + c <= myG o0 m0)%ord
  (O: (o1 < o0)%ord)  -> (myF o1 + e <= myH o0)%ord
   ***)

  Let NZERO: (Ord.O < alpha * kappa + c)%ord.
  Proof.
    unfold alpha.

    assert(T: (1 < f + 3 + d + e)%ord).
    { assert(U: (1 + 1 <= (Ord.from_nat 3))%ord).
      { rewrite <- OrdArith.add_from_nat. ss. eapply OrdArith.le_from_nat; et. }
      eapply Ord.lt_le_lt; cycle 1.
      { rewrite <- U. refl. }
      rewrite ! OrdArith.add_assoc.
      eapply Ord.lt_le_lt; cycle 1.
      { eapply OrdArith.add_base_r. }
      eapply OrdArith.add_lt_l.
      rewrite Ord.from_nat_S at 1.
      eapply Ord.lt_le_lt.
      { instantiate (1:=1%ord). rewrite Ord.from_nat_S. eapply Ord.S_pos. }
      { rewrite Ord.from_nat_S. eapply OrdArith.add_base_l. }
    }

    eapply Ord.lt_le_lt; cycle 1.
    { eapply OrdArith.add_base_l. }
    rewrite <- OrdArith.mult_1_r.
    eapply Ord.le_lt_lt; cycle 1.
    { instantiate (1:=((f + 3 + d + e) * 1)%ord).
      eapply OrdArith.lt_mult_r.
      - eauto with ord_kappa.
      - rewrite <- T. replace (Ord.from_nat 1) with (Ord.S Ord.O) by ss. eapply Ord.S_pos. }
    eapply mult_le_le.
    - eapply Ord.O_is_O.
    - refl.
  Qed.

  Global Program Instance myG_proper: Proper (Ord.le ==> Ord.le ==> Ord.le) (myG).
  Next Obligation.
    ii. unfold myG.
    rewrite <- H0.
    eapply mult_le_le; et; try refl.
    eapply mult_le_le; et; try refl.
    rewrite <- H. refl.
  Qed.

  Theorem my_thm1: forall o0, (myG o0 kappa + c <= myF o0)%ord.
  Proof.
    i. unfold myF, myG, myH.
    rewrite OrdArith.expn_add; et.
    rewrite OrdArith.expn_1_r; et.
    rewrite OrdArith.mult_dist.
    eapply add_le_le.
    - rewrite <- OrdArith.mult_assoc. refl.
    - rewrite <- (OrdArith.mult_1_l) at 1. eapply mult_le_le; try refl. eapply expn_pos.
    (* OrdArith.add *)
    (* OrdArith.mult *)
    (* OrdArith.expn *)
  Qed.

  Theorem my_thm3
          o0 o1
          (O: (o1 < o0)%ord)
    :
      (myF o1 + e <= myH o0)%ord
  .
  Proof.
    unfold myF, myG, myH.
    eapply add_one_lt in O.
    rewrite <- O.
    rewrite OrdArith.expn_add; et.
    rewrite OrdArith.expn_1_r; et.
    assert(T: (1 + 1 <= 3)%ord).
    { rewrite <- OrdArith.add_from_nat. ss. eapply OrdArith.le_from_nat; et. }
    rewrite <- T.
    rewrite OrdArith.mult_dist with (o2:=1).
    rewrite OrdArith.mult_1_r.
    eapply add_le_le; try refl.
    rewrite <- (OrdArith.mult_1_l) at 1.
    eapply mult_le_le.
    { eapply expn_pos. }
    rewrite <- alpha_e.
    etrans; [|eapply OrdArith.add_base_l].
    rewrite <- (OrdArith.mult_1_r) at 1.
    eapply mult_le_le; try refl.
    eapply Ord.lt_le.
    eauto with ord_kappa.
  Qed.

  Theorem my_thm2
          o0 m0 m1
          (AM: (m1 < m0)%ord)
    :
      (myG o0 m1 + f + myH o0 + d <= myG o0 m0)%ord
  .
  Proof.
    unfold myF, myG, myH.
    eapply add_one_lt in AM.
    rewrite <- AM.
    rewrite OrdArith.mult_dist.
    rewrite OrdArith.mult_1_r.
    rewrite OrdArith.add_assoc.
    rewrite OrdArith.add_assoc.
    eapply add_le_le; try refl.
    rewrite <- alpha_d at 3.
    rewrite OrdArith.mult_dist.
    rewrite OrdArith.mult_dist.
    rewrite <- OrdArith.add_assoc.
    eapply add_le_le; try refl; cycle 1.
    { rewrite <- (OrdArith.mult_1_l) at 1. eapply mult_le_le; try refl. eapply expn_pos. }
    eapply add_le_le; try refl; cycle 1.
    { rewrite <- (OrdArith.mult_1_l) at 1. eapply mult_le_le; try refl. eapply expn_pos. }
  Qed.

  End CONSTRUCTION.

End Construction.


Module MyParam <: PARAM.
  Definition d: Ord.t := 50%ord.
  Definition c: Ord.t := (d + 30)%ord.
  Definition e: Ord.t := 50%ord.
  Definition f: Ord.t := (d + 10)%ord.
End MyParam.

Module C := (Construction MyParam).












(* Lemma upcast_ty: forall T (v: T), Any.ty v↑ = T. admit "ez". Qed. *)
(* Lemma upcast_val: forall T (v: T), Any.val v↑ ~= v. admit "ez". Qed. *)






Inductive opair: Type := mk_opair { ofst: Ord.t; osnd: Ord.t }.
(* Definition opair_lt: opair -> opair -> Prop := fun '(mk_opair x0 x1) '(mk_opair y0 y1) => (x0 < y0)%ord \/ (x0 == y0 /\ x1 < y1)%ord. *)
Inductive opair_lt: opair -> opair -> Prop :=
| intro_opair_lt
    x0 x1 y0 y1
    (LT: (x0 < y0)%ord \/ (x0 == y0 /\ x1 < y1)%ord)
  :
    opair_lt (mk_opair x0 x1) (mk_opair y0 y1)
.
Theorem wf_opair_lt: well_founded opair_lt.
Proof.
  ii. destruct a.
  revert osnd0. pattern ofst0. eapply well_founded_ind. { eapply Ord.lt_well_founded. } clear ofst0. intros ? IH0.
  intro. generalize dependent x. pattern osnd0. eapply well_founded_ind. { eapply Ord.lt_well_founded. } clear osnd0. intros ? IH1.
  econs. i. inv H. des.
  { eapply IH0; et. }
  { eapply IH1; et. i. eapply IH0; et. rewrite <- LT. ss. }
Qed.











Section CANCEL.

  (*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
  Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)



  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.

  Let sk: Sk.t := fold_right Sk.add Sk.unit (List.map SMod.sk mds).
  (* Let skenv: SkEnv.t := Sk.load_skenv sk. *)
  Let mss: list SModSem.t := (List.map ((flip SMod.get_modsem) sk) mds).
  Let sbtb: list (gname * fspecbody) := (List.flat_map (SModSem.fnsems) mss).
  Let stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb.

  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Let mds_mid: list Mod.t := List.map (SMod.to_mid stb) mds.



  Let W: Type := (r_state * p_state).
  (* Let wf: Ord.t -> W -> W -> Prop := top3. *)

  Opaque EventsL.interp_Es.

  Let ms_src: ModSemL.t := ModL.enclose (Mod.add_list mds_src).
  Let ms_mid: ModSemL.t := ModL.enclose (Mod.add_list mds_mid).

  Let p_src := ModSemL.prog ms_src.
  Let p_mid := ModSemL.prog ms_mid.

  Ltac _step :=
    match goal with
    (*** terminal cases ***)
    | [ |- gpaco5 _ _ _ _ _ _ _ (triggerUB >>= _) _ ] =>
      unfold triggerUB; mred; _step; ss; fail
    | [ |- gpaco5 _ _ _ _ _ _ _ (triggerNB >>= _) _ ] =>
      exfalso
    | [ |- gpaco5 _ _ _ _ _ _ _ _ (triggerUB >>= _) ] =>
      exfalso
    | [ |- gpaco5 _ _ _ _ _ _ _ _ (triggerNB >>= _) ] =>
      unfold triggerNB; mred; _step; ss; fail

    (*** assume/guarantee ***)
    | [ |- gpaco5 _ _ _ _ _ _ _ (assume ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco5 _ _ _ _ _ _ _ (guarantee ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar
    | [ |- gpaco5 _ _ _ _ _ _ _ _ (assume ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco5 _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar

    (*** default cases ***)
    | _ =>
      (gstep; econs; eauto; try (eapply add_le_lt; [refl|eapply OrdArith.lt_from_nat; ss]);
       (*** some post-processing ***)
       i;
       try match goal with
           | [ |- (eq ==> _)%signature _ _ ] =>
             let v_src := fresh "v_src" in
             let v_tgt := fresh "v_tgt" in
             intros v_src v_tgt ?; subst v_tgt
           end)
    end
  .

  Ltac steps := repeat (mred; try _step; des_ifs_safe).

Let adequacy_type_aux__APC:
    forall at_most o0 mn
           st_src0 st_tgt0
    ,
      simg (fun _ '(st_tgt1, _) => st_tgt1 = st_tgt0)
           (C.myG o0 at_most + C.d)%ord (Ret (st_src0, tt))
           (EventsL.interp_Es p_mid (transl_all mn (interp_hCallE_mid stb (ord_pure o0) (_APC at_most))) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
    (* induction *)
    intros ? ?. remember (mk_opair o0 at_most) as fuel. move fuel at top. revert at_most o0 Heqfuel.
    pattern fuel. eapply well_founded_induction. { eapply wf_opair_lt. } clear fuel.
    intros fuel IH. i.

    rewrite unfold_APC. destruct st_tgt0 as [rst_tgt0 pst_tgt0]. steps.
    destruct x.
    { steps. }
    steps. destruct (alist_find s stb) eqn:EQ; ss.
    2: { steps. }
    destruct rst_tgt0 as [mrs_tgt0 [|frs_hd frs_tl]]; ss.
    { steps. destruct (Any.downcast t0); steps. }
    steps. destruct (Any.downcast t0); ss.
    2:{ steps. }
    steps. unfold unwrapU. des_ifs; cycle 1.
    { exfalso. hexploit (stb_find_iff s). rewrite EQ. rewrite Heq. clear. intuition. }
    unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
    unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
    rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
    rename Heq0 into INF. rename Heq into IN.
    rename x3 into md0. fold sk in INF. fold sk in INF.
    unfold fun_to_mid.
    steps. assert (f0.(fsb_fspec) = f).
    { admit "fspec table". }
    subst. rewrite Any.upcast_downcast. steps.
    guclo ordC_spec. econs.
    { eapply OrdArith.add_base_l. }
    guclo ordC_spec. econs.
    { eapply C.my_thm2; et. }
    guclo ordC_spec. econs.
    { rewrite OrdArith.add_assoc. refl. }
    rewrite idK_spec at 1.
    guclo bindC_spec. econs.
    { unfold APC. gstep. mred. eapply simg_chooseR; et; [_ord_step|]. i. steps.
      guclo ordC_spec. econs.
      { instantiate (1:=(C.myG x1 x3 + C.d)%ord).
        rewrite <- C.my_thm3; et.
        rewrite <- C.my_thm1; et.
        rewrite OrdArith.add_assoc.
        rewrite OrdArith.add_assoc.
        eapply add_le_le.
        - eapply Ord.lt_le in x4. rewrite <- x4. refl.
        - etrans; [|eapply OrdArith.add_base_l]. etrans; [|eapply OrdArith.add_base_l]. refl.
      }
      eapply IH; auto. econs. left. auto.
    }

    i. ss. destruct vret_tgt as [? []]. destruct vret_src as [? []]. ss. des; subst.
    unfold idK. unfold C.f.
    guclo ordC_spec. econs.
    { rewrite <- OrdArith.add_assoc. refl. }
    steps.
    guclo ordC_spec. econs.
    { eapply OrdArith.add_base_l. }
    { eapply IH; et. econs; et. right; split; et. refl. }
  Qed.


  Let adequacy_type_aux__APC:
    forall at_most o0 mn
           st_src0 st_tgt0
    ,
      simg (fun _ '(st_tgt1, _) => st_tgt1 = st_tgt0)
           (C.myG o0 at_most + C.d)%ord
           (Ret (st_src0, tt))
           (EventsL.interp_Es p_mid (transl_all mn (interp_hCallE_mid stb (ord_pure o0) (_APC at_most))) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
    intros ? ?. remember (mk_opair o0 at_most) as fuel. move fuel at top. revert at_most o0 Heqfuel.
    pattern fuel. eapply well_founded_induction. { eapply wf_opair_lt. } clear fuel.
    intros fuel IH.
    i. rewrite unfold_APC.
    destruct st_tgt0 as [rst_tgt0 pst_tgt0]. destruct rst_tgt0 as [mrs_tgt0 [|frs_hd frs_tl]]; ss.
    { admit "-----------------------------------it should not happen...". }
    unfold C.d.
    steps.
    destruct x.
    { steps. }
    steps.
    (*************** TODO: define force_l/r *************)
    unfold unwrapU. des_ifs; cycle 1.
    { admit "-----------------------------------FINDF: make it to unwrapN". }
    steps.
    unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
    unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
    rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
    rename Heq0 into INF. rename Heq into IN.
    rename x3 into md0. fold sk in INF. fold sk in INF.
    unfold fun_to_mid.
    steps.
    unfold unwrapN.
    des_ifs; cycle 1.
    { steps. }
    steps.
    des_ifs_safe.
    eapply pair_downcast_lemma in Heq. des. subst.
    des_ifs; ss.
    steps.

    guclo ordC_spec. econs.
    { eapply OrdArith.add_base_l. }
    guclo ordC_spec. econs.
    { eapply C.my_thm2; et. }
    guclo ordC_spec. econs.
    { rewrite OrdArith.add_assoc. refl. }
    rewrite idK_spec at 1.
    guclo bindC_spec. econs.
    {
      Local Transparent APC.
      unfold APC.
      steps.
      guclo ordC_spec. econs.
      { instantiate (1:=(C.myG x1 x3 + C.d)%ord).
        rewrite <- C.my_thm3; et.
        rewrite <- C.my_thm1; et.
        rewrite OrdArith.add_assoc.
        rewrite OrdArith.add_assoc.
        eapply add_le_le.
        - eapply Ord.lt_le in x4. rewrite <- x4. refl.
        - etrans; [|eapply OrdArith.add_base_l]. etrans; [|eapply OrdArith.add_base_l]. refl.
      }
      eapply IH; et. econs; et.
    }
    i. ss. des_ifs. destruct vret_src; ss. repeat des_u. unfold idK.
    unfold C.f.
    guclo ordC_spec. econs.
    { rewrite <- OrdArith.add_assoc. refl. }
    steps.
    guclo ordC_spec. econs; cycle 1.
    { eapply IH; et. econs; et. right; split; et. refl. }
    { eapply OrdArith.add_base_l. }
  Qed.

  Let adequacy_type_aux_APC:
    forall o0 st_src0 st_tgt0 mn
    ,
      simg (fun _ '(st_tgt1, _) => st_tgt1 = st_tgt0)
           (C.myF o0)%ord (Ret (st_src0, tt))
           (EventsL.interp_Es p_mid (transl_all mn (interp_hCallE_mid (ord_pure o0) APC)) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
    i. unfold APC.
    guclo ordC_spec. econs.
    { rewrite <- C.my_thm1. refl. }
    unfold C.c.
    guclo ordC_spec. econs.
    { rewrite <- OrdArith.add_assoc. refl. }
    steps.
    guclo ordC_spec. econs.
    { etrans; [|eapply OrdArith.add_base_l]. eapply add_le_le; [|refl].
      instantiate (1:=C.myG o0 x).
      eapply Ord.lt_le in x0. rewrite <- x0. refl. }
    gfinal. right.
    eapply adequacy_type_aux__APC.
  Qed.

  Lemma idK_spec2: forall E A B (a: A) (itr: itree E B), itr = Ret a >>= fun _ => itr. Proof. { i. ired. ss. } Qed.

  Definition formula (o0: ord): Ord.t :=
    match o0 with
    | ord_pure o0 => (10 + C.myF o0)%ord
    | ord_top => 100%ord
    end
  .

  Let wf: W -> W -> Prop := fun '(_, pst_src0) '(_, pst_tgt0) => pst_src0 = pst_tgt0.
  Let wf': forall {X}, (W * X)%type -> (W * X)%type -> Prop := (fun _ '(st_src0, rv_src) '(st_tgt0, rv_tgt) => wf st_src0 st_tgt0 /\ rv_src = rv_tgt).

  Let adequacy_type_aux:
    forall
      AA AR
      args
      o0
      body st_src0 st_tgt0 mn
      (SIM: wf st_src0 st_tgt0)
    ,
      simg wf'
           (formula o0 + 10)%ord
           (* (if is_pure o0 then trigger (Choose _) else (interp_Es p_src ((fun_to_src (AA:=AA) (AR:=AR) body) args↑) st0)) *)
           (EventsL.interp_Es p_src (transl_all mn (if is_pure o0 then trigger (Choose _) else ((fun_to_src (AA:=AA) (AR:=AR) body) args))) st_src0)
           (EventsL.interp_Es p_mid (transl_all mn ((fun_to_mid body) (Any.pair o0↑ args))) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
    gcofix CIH. i.
    unfold fun_to_src, fun_to_mid. steps. unfold unwrapN.
    destruct (Any.downcast (Any.pair (Any.upcast o0) args)) eqn:T; cycle 1.
    { steps. }
    destruct p.
    eapply pair_downcast_lemma in T. des; subst; ss. eapply Any.downcast_upcast in T0. des; subst.
    unfold body_to_src, cfun. steps. rewrite Any.upcast_downcast. ss. steps.
    destruct o; ss.
    - (*** PURE ***)
      seal_left.
      steps.
      unseal_left.
      erewrite idK_spec2 at 1.
      guclo ordC_spec. econs.
      { eapply OrdArith.add_base_l. }
      guclo bindC_spec.
      econs.
      { gfinal. right. eapply paco5_mon. { eapply adequacy_type_aux_APC. } ii; ss. }
      ii; ss. des_ifs. des_u.
      steps. esplits; eauto. steps.
    - (*** IMPURE ***)
      steps. unfold body_to_mid.
      abstr (body a) itr. clear body a AA.

      guclo ordC_spec. econs.
      { instantiate (1:=(10 + 100)%ord). rewrite <- ! OrdArith.add_from_nat. ss. refl. }
      (* { instantiate (1:=(1 + 99)%ord). rewrite <- OrdArith.add_from_nat. ss. refl. } *)
      guclo bindC_spec. eapply bindR_intro with (RR:=wf'); cycle 1.
      { ii. subst. des_ifs. steps. r in SIM0. des; subst; ss. }

      revert_until CIH. gcofix CIH0. i.

      ides itr.
      { steps. }
      { steps. gbase. eapply CIH0; ss. }
      destruct e; cycle 1.
      {

        (*** TODO: remove redundancy with Hoareproof0 ***)
  Ltac resub :=
    repeat multimatch goal with
           | |- context[ITree.trigger ?e] =>
             match e with
             | subevent _ _ => idtac
             | _ => replace (ITree.trigger e) with (trigger e) by refl
             end
           | |- context[@subevent _ ?F ?prf _ (?e|)%sum] => replace (@subevent _ F prf _ (e|)%sum) with (@subevent _ F _ _ e) by refl
           | |- context[@subevent _ ?F ?prf _ (|?e)%sum] => replace (@subevent _ F prf _ (|e)%sum) with (@subevent _ F _ _ e) by refl
           end.
        rewrite <- bind_trigger. resub. steps.
        destruct s; ss.
        {
          destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
          destruct p; ss.
          - steps. instantiate (1:=100). gbase. eapply CIH0; ss; et.
          - steps. instantiate (1:=100). gbase. eapply CIH0; ss; et.
        }
        { dependent destruction e.
          - steps. unshelve esplits; et. instantiate (1:=100). steps. gbase. eapply CIH0; ss; et.
          - steps. unshelve esplits; et. instantiate (1:=100). steps. gbase. eapply CIH0; ss; et.
          - steps. unshelve esplits; et. instantiate (1:=100). steps. gbase. eapply CIH0; ss; et.
        }
      }
      dependent destruction h.
      rewrite <- bind_trigger. resub.
      Opaque fun_to_src fun_to_mid.

      destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
      ired_both.
      destruct tbr.
      + (*** PURE CALL ***)
        mred.
        seal_left.
        Ltac step := (mred; try _step; des_ifs_safe).
        step; try by eapply OrdArith.lt_from_nat.
        step; try by eapply OrdArith.lt_from_nat.
        unseal_left.
        step; try by eapply OrdArith.lt_from_nat.
        instantiate (1:=(120 + formula (ord_pure x) + 100)%ord).
        seal_left.

        steps.
        destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]]; ss.
        { unseal_left. steps. }
        steps.
        unfold unwrapU. des_ifs; cycle 1.
        { admit "unwrapN!!!!!!!!!!!!!!!!!!!!!!!!!!". }
        steps.
        unseal_left.
        unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
        unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
        rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
        rename Heq0 into INF. rename Heq into IN.
        rename x1 into md0. fold sk in INF. fold sk in INF.
        mred.
        guclo ordC_spec. econs.
        { instantiate (1:=(120 + (10 + C.myF x + 10))%ord).
          rewrite <- ! OrdArith.add_assoc. eapply add_le_le; try refl. eapply OrdArith.le_from_nat; ss. lia. }
        rename x into o1.
        rewrite <- bind_bind.
        rewrite <- bind_bind.
        guclo bindC_spec. econs.
        * (* guclo ordC_spec. econs. *)
          (* { eapply OrdArith.add_base_r. } *)
          (* gbase. eapply CIH; et. *)
          gbase. hexploit CIH; et.
          { instantiate (1:=(mrs_tgt0, ε :: frs_tgt_hd :: frs_tgt_tl, pst_tgt0)). instantiate (1:= (rst_src0, pst_tgt0)). ss. }
          intro T. instantiate (2:=(ord_pure o1)) in T. ss.
          mred.
          (*** applying reduction in "T" begin ***)
          (*** TODO: make prw "in" tactic ***)
          revert T. pose (fun (x: Prop) (y: Prop) => (x -> y)) as myf.
          match goal with | |- ?a -> ?b => replace (a -> b) with (myf a b) by refl end.
          try Red.prw ltac:(IRed._red_gen) 2 2 0.
          subst myf; cbn. intro T.
          (*** applying reduction in "T" end ***)
          eapply T.
        * ii. des_ifs. destruct p, p0; ss. des; subst.
          step; try by eapply OrdArith.lt_from_nat. steps.
          destruct r1; ss.
          des_ifs.
          { unfold triggerNB. steps; try by eapply OrdArith.lt_from_nat. (*** TODO: fix tactic, don't unfold triggerNB ***) }
          repeat (step; try by eapply OrdArith.lt_from_nat).
          guclo ordC_spec. econs.
          { instantiate (1:=100%ord). eapply OrdArith.le_from_nat; ss. lia. }
          gbase. eapply CIH0. ss.
      + (*** IMPURE CALL ***)
        mred.
        destruct rst_src0 as [mrs_src0 [|frs_src_hd frs_src_tl]]; ss.
        { admit "SOMEHOW". }
        mred. steps. instantiate (2:=(100 + (100 + 10) + 42)%ord). instantiate (1:=0%ord).
        guclo ordC_spec. econs. { rewrite OrdArith.add_O_r. refl. }
        destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]]; ss.
        { steps. }
        steps. unfold unwrapU at 2. des_ifs; cycle 1.
        { admit "unwrapN!!!!!!!!!!!!!!!!!!". }
        steps.
        unfold unwrapU. des_ifs; cycle 1.
        { steps. }
        steps.

        unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
        unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
        rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq1. des; ss. des_ifs. ss; des; ss; clarify.
        rename Heq1 into INF. rename Heq into IN.
        rename x0 into md0. fold sk in INF. fold sk in INF.

        unfold ms_src, mds_src, SMod.to_src in Heq0. rewrite SMod.transl_fnsems in Heq0.
        unfold SMod.load_fnsems in Heq0. apply find_some in Heq0. des; ss. des_sumbool; subst.
        rewrite in_flat_map in Heq0. des; ss. rewrite in_flat_map in Heq1. des; ss. des_ifs. ss; des; ss; clarify.
        rename Heq1 into INF0. rename Heq0 into IN0.
        rename x0 into md1. fold sk in INF0. fold sk in INF0.

        assert(md0 = md1); subst.
        { admit "ez - uniqueness". }

        assert(f = f0); subst.
        { admit "ez - uniqueness". }

        guclo ordC_spec. econs.
        { eapply OrdArith.add_base_l. }
        guclo bindC_spec.
        econs.
        * hexploit CIH; et; cycle 1.
          { intro T. gbase. instantiate (3:=ord_top) in T. ss. eapply T. }
          { ss. }
        * ii; ss. des_ifs. steps. destruct p, p0; ss. des; subst.
          steps. destruct r1; ss. des_ifs.
          { unfold triggerNB. (step; try by eapply OrdArith.lt_from_nat). (*** TODO: fix tactic ***) }
          destruct r0; ss. des_ifs. { admit "somehow". } steps.
          instantiate (1:=100).
          gbase. eapply CIH0 ;ss.
  Unshelve.
    all: try (by econs; et).
    all: try (by exact Ord.O).
    all: ss.
  Unshelve.
    all: try (by exact unit).
  Qed.

  Theorem adequacy_type_m2s: Beh.of_program (ModL.compile (Mod.add_list mds_mid)) <1=
                             Beh.of_program (ModL.compile (Mod.add_list mds_src)).
  Proof.
    eapply adequacy_global.
    exists (100)%ord. ss.
    ginit.
    { eapply cpn5_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr. Local Opaque ModSemL.prog. ss.
    unfold ITree.map.
    unfold assume.
    steps.
    instantiate (1:=(10 + (100 + 10) + 42)%ord).
    esplits; et. { admit "ez - wf". } steps.
    Local Transparent ModSemL.prog.
    unfold ModSemL.prog at 4.
    unfold ModSemL.prog at 2.
    Local Opaque ModSemL.prog.
    ss. steps.
    (* Opaque ModSemL.initial_r_state. *)
    (* Opaque ModSemL.initial_p_state. *)
    fold ms_src. fold ms_mid.
    set (rs_src0 := initial_r_state ms_src) in *.
    set (rs_tgt0 := initial_r_state ms_mid) in *.
    assert(exists mrs_src0 hd_src tl_src, rs_src0 = (mrs_src0, hd_src :: tl_src)).
    { esplits. refl. }
    assert(exists mrs_tgt0 hd_tgt tl_tgt, rs_tgt0 = (mrs_tgt0, hd_tgt :: tl_tgt)).
    { esplits. refl. }
    des. clearbody rs_src0 rs_tgt0. subst.
    unfold unwrapU at 1. des_ifs; cycle 1.
    { steps. }
    unfold unwrapU. des_ifs; cycle 1.
    { admit "unwrapN!!!!!!!!!!". }


    unfold ms_mid, mds_mid, SMod.to_mid in Heq0. rewrite SMod.transl_fnsems in Heq0.
    unfold SMod.load_fnsems in Heq0. apply find_some in Heq0. des; ss. des_sumbool; subst.
    rewrite in_flat_map in Heq0. des; ss. rewrite in_flat_map in Heq2. des; ss. des_ifs. ss; des; ss; clarify. ss. subst.
    rename Heq2 into INF. rename Heq0 into IN.
    rename x into md0. fold sk in INF. fold sk in INF.

    unfold ms_src, mds_src, SMod.to_src in Heq. rewrite SMod.transl_fnsems in Heq.
    unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. destruct p; ss. des_sumbool; subst.
    rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
    rename Heq0 into INF0. rename Heq into IN0.
    rename x into md1. fold sk in INF0. fold sk in INF0.

    assert(md0 = md1); subst.
    { admit "ez - uniqueness". }
    assert(f = f0).
    { admit "ez - uniqueness". }
    subst.
    fold ms_src. fold ms_mid. fold p_src. fold p_mid.

    steps.

    match goal with
    | [ |- gpaco5 _ _ _ _ _ _ _ ?i_src _ ] => remember i_src as tmp
    end.
    replace (([]: list val)↑) with (Any.pair ord_top↑ ([]: list val)↑) by admit "TODO".
    subst tmp.

    guclo ordC_spec. econs.
    { eapply OrdArith.add_base_l. }
    guclo bindC_spec.
    econs.
    - hexploit adequacy_type_aux; cycle 1.
      { intro T. gfinal. right. instantiate (3:=ord_top) in T. ss. eapply T. }
      ss. unfold ms_src, ms_mid. unfold initial_p_state.
      apply func_ext. intro mn. unfold mds_src, mds_mid, SMod.to_src, SMod.to_mid.
      rewrite ! SMod.transl_initial_mrs. ss.
    - ii. rr in SIM. des_ifs. des; ss. subst. r in SIM. des_ifs. steps.
  Unshelve.
    all: ss.
    all: try (by exact Ord.O).
    all: try (by econs; et).
  Qed.

End CANCEL.

Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Import ModSemL.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef.
Require Import SimSTS.
Require Import SimGlobal.
Require Import HoareDef.
From Ordinal Require Import Ordinal Arithmetic.

Set Implicit Arguments.
















Inductive _simg_safe (simg: forall R (RR: R -> R -> Prop), Ord.t -> (itree eventE R) -> (itree eventE R) -> Prop)
          {R} (RR: R -> R -> Prop) (i0: Ord.t): (itree eventE R) -> (itree eventE R) -> Prop :=
| simg_safe_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    _simg_safe simg RR i0 (Ret r_src) (Ret r_tgt)
| simg_safe_syscall
    i1 ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: (eq ==> simg _ RR i1)%signature ktr_src0 ktr_tgt0)
  :
    _simg_safe simg RR i0 (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)



| simg_safe_tau
    i1 itr_src0 itr_tgt0
    (TAUBOTH: True)
    (* (ORD: Ordinal.le i1 i0) *)
    (SIM: simg _ RR i1 itr_src0 itr_tgt0)
  :
    _simg_safe simg RR i0 (tau;; itr_src0) (tau;; itr_tgt0)
| simg_safe_tauL
    i1 itr_src0 itr_tgt0
    (TAUL: True)
    (ORD: Ord.lt i1 i0)
    (SIM: simg _ RR i1 itr_src0 itr_tgt0)
  :
    _simg_safe simg RR i0 (tau;; itr_src0) (itr_tgt0)
| simg_safe_tauR
    i1 itr_src0 itr_tgt0
    (TAUR: True)
    (ORD: Ord.lt i1 i0)
    (SIM: simg _ RR i1 itr_src0 itr_tgt0)
  :
    _simg_safe simg RR i0 (itr_src0) (tau;; itr_tgt0)



| simg_safe_chooseR
    i1 X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (ORD: Ord.lt i1 i0)
    (SIM: forall x, simg _ RR i1 itr_src0 (ktr_tgt0 x))
  :
    _simg_safe simg RR i0 (itr_src0) (trigger (Choose X) >>= ktr_tgt0)



| simg_safe_takeL
    i1 X ktr_src0 itr_tgt0
    (TAKEL: True)
    (ORD: Ord.lt i1 i0)
    (SIM: forall x, simg _ RR i1 (ktr_src0 x) itr_tgt0)
  :
    _simg_safe simg RR i0 (trigger (Take X) >>= ktr_src0) (itr_tgt0)



(* | simg_stutter *)
(*     i1 itr_src itr_tgt *)
(*     (ORD: Ord.lt i1 i0) *)
(*     (SIM: simg _ RR i1 itr_src itr_tgt) *)
(*   : *)
(*     simg_safe simg RR i0 itr_src itr_tgt *)
.

Lemma simg_safe_spec:
  _simg_safe <6= _simg.
Proof. i. inv PR; try by (econs; eauto). Qed.


















(* Program Instance ord_lt_proper: Proper (Ord.eq ==> Ord.eq ==> eq) Ord.lt. *)
(* Next Obligation. *)
(*   ii. *)
(*   apply prop_ext. split; i. *)
(*   - eapply Ord.lt_eq_lt. { sym. et. } eapply Ord.eq_lt_lt; et. sym. et. *)
(*   - eapply Ord.lt_eq_lt; et. eapply Ord.eq_lt_lt; et. *)
(* Qed. *)

Program Instance lt_proper: Proper (Ord.eq ==> Ord.eq ==> iff) (Ord.lt).
Next Obligation.
  ii.
  split; i.
  - eapply Ord.lt_eq_lt. { sym. et. } eapply Ord.eq_lt_lt; et. sym. et.
  - eapply Ord.lt_eq_lt; et. eapply Ord.eq_lt_lt; et.
Qed.

Program Instance le_proper: Proper (Ord.eq ==> Ord.eq ==> iff) (Ord.le).
Next Obligation.
  ii.
  split; i.
  - eapply Ord.le_eq_le. { sym. et. } eapply Ord.eq_le_le; et. sym. et.
  - eapply Ord.le_eq_le; et. eapply Ord.eq_le_le; et.
Qed.

Program Instance expn_proper: Proper (Ord.eq ==> Ord.eq ==> Ord.eq) (OrdArith.expn).
Next Obligation.
  ii.
  etrans.
  - eapply OrdArith.eq_expn_l; et.
  - eapply OrdArith.eq_expn_r; et.
Qed.

Program Instance expn_le_proper: Proper (Ord.le ==> Ord.le ==> Ord.le) (OrdArith.expn).
Next Obligation.
  ii.
  etrans.
  - eapply OrdArith.le_expn_l; et.
  - eapply OrdArith.le_expn_r; et.
Qed.

Program Instance add_proper: Proper (Ord.eq ==> Ord.eq ==> Ord.eq) (OrdArith.add).
Next Obligation.
  ii.
  etrans.
  - eapply OrdArith.eq_add_l; et.
  - eapply OrdArith.eq_add_r; et.
Qed.

Program Instance add_le_proper: Proper (Ord.le ==> Ord.le ==> Ord.le) (OrdArith.add).
Next Obligation.
  ii.
  etrans.
  - eapply OrdArith.le_add_l; et.
  - eapply OrdArith.le_add_r; et.
Qed.

(* Program Instance add_lt_proper: Proper (Ord.le ==> Ord.lt ==> Ord.lt) (OrdArith.add). *)
(* Next Obligation. *)
(*   ii. *)
(*   eapply Ord.le_lt_lt. *)
(*   - rewrite H. refl. *)
(*   - eapply OrdArith.lt_add_r; et. *)
(* Qed. *)

Program Instance mult_eq_proper: Proper (Ord.eq ==> Ord.eq ==> Ord.eq) (OrdArith.mult).
Next Obligation.
  ii.
  etrans.
  - eapply OrdArith.eq_mult_l; et.
  - eapply OrdArith.eq_mult_r; et.
Qed.

Program Instance mult_le_proper: Proper (Ord.le ==> Ord.le ==> Ord.le) (OrdArith.mult).
Next Obligation.
  ii.
  etrans.
  - eapply OrdArith.le_mult_l; et.
  - eapply OrdArith.le_mult_r; et.
Qed.

Program Instance S_proper: Proper (Ord.eq ==> Ord.eq) (Ord.S).
Next Obligation.
  ii.
  eapply Ord.eq_S; et.
Qed.

(* Program Instance eq_proper: Proper (Ord.eq ==> Ord.eq ==> Ord.eq) (Ord.lt). *)
(* Next Obligation. *)
(*   ii. *)
(*   split; i. *)
(*   - eapply Ord.lt_eq_lt. { sym. et. } eapply Ord.eq_lt_lt; et. sym. et. *)
(*   - eapply Ord.lt_eq_lt; et. eapply Ord.eq_lt_lt; et. *)
(* Qed. *)

(* Theorem ord_pow_one: forall o0, (o0 ^ 1 == o0)%ord. *)
(* Proof. *)
(*   i. *)
(*   unfold OrdArith.expn. *)
(*   rewrite <- (OrdArith.add_O_r 1%ord). *)
(*   rewrite OrdArith.expn_add. *)
(*   replace (Ord.from_nat 1) with (1 + 0)%ord; cycle 1. *)
(*   { rewrite OrdArith.add_O_r. Ord.add_0_r. *)
(*   Set Printing All. *)
(*   ss. *)
(*   replace (1%ord) with (Ord.O + (1%ord))%ord. by ss. *)
(*   etrans. rewrite OrdArith.expn_add. *)
(* Qed. *)

Lemma add_le_lt: forall x0 x1 y0 y1, (x0 <= x1)%ord -> (y0 < y1)%ord -> (x0 + y0 < x1 + y1)%ord.
Proof.
  i.
  eapply Ord.le_lt_lt.
  - eapply OrdArith.le_add_l; et.
  - eapply OrdArith.lt_add_r; et.
Qed.

Lemma add_le_le: forall x0 x1 y0 y1, (x0 <= x1)%ord -> (y0 <= y1)%ord -> (x0 + y0 <= x1 + y1)%ord.
Proof.
  i.
  etrans.
  - eapply OrdArith.le_add_r; et.
  - eapply OrdArith.le_add_l; et.
Qed.

Lemma mul_le_lt: forall x0 x1 y0 y1, (0 < x1)%ord -> (x0 <= x1)%ord -> (y0 < y1)%ord -> (x0 * y0 < x1 * y1)%ord.
Proof.
  i.
  eapply Ord.le_lt_lt.
  - eapply OrdArith.le_mult_l; et.
  - eapply OrdArith.lt_mult_r; et.
Qed.

Lemma mult_le_le: forall x0 x1 y0 y1, (x0 <= x1)%ord -> (y0 <= y1)%ord -> (x0 * y0 <= x1 * y1)%ord.
Proof.
  i.
  etrans.
  - eapply OrdArith.le_mult_l; et.
  - eapply OrdArith.le_mult_r; et.
Qed.

Lemma expn_pos: forall base o, (1 <= base ^ o)%ord.
Proof. i. rewrite Ord.from_nat_S. eapply Ord.S_supremum. eapply OrdArith.expn_pos. Qed.

Lemma add_one_lt: forall o0 o1, (o0 < o1)%ord -> (o0 + 1 <= o1)%ord.
Proof.
  i.
  rewrite Ord.from_nat_S.
  rewrite OrdArith.add_S.
  rewrite OrdArith.add_O_r.
  eapply Ord.S_supremum; et.
Qed.






Module Type PARAM.
  Parameter c: Ord.t.
  Parameter d: Ord.t.
  Parameter e: Ord.t.
  Parameter f: Ord.t.
End PARAM.

Module Construction (P: PARAM).
  Include P.

  Section CONSTRUCTION.

  Let alpha := (f + 3 + d + e)%ord.
  (* Let alpha_d: ((1 + d) <= alpha)%ord. *)
  (* Proof. unfold alpha. rewrite <- OrdArith.add_O_r at 1. eapply add_le_le; try refl. eapply Ord.O_is_O. Qed. *)
  Let alpha_e: (e <= alpha)%ord.
  Proof.
    unfold alpha.
    eapply OrdArith.add_base_r.
    (* etrans; [eapply OrdArith.add_base_l|]. *)
    (* etrans; [eapply OrdArith.add_base_r|]. *)
    (* rewrite <- OrdArith.add_assoc. rewrite OrdArith.add_assoc. refl. *)
  Qed.

  Let alpha_d: (f + 3 + d <= alpha)%ord.
  Proof.
    unfold alpha.
    eapply OrdArith.add_base_l.
    (* etrans; [eapply OrdArith.add_base_l|]. *)
    (* etrans; [eapply OrdArith.add_base_r|]. *)
    (* rewrite <- OrdArith.add_assoc. *)
    (* eapply add_le_le; try refl. *)
    (* rewrite <- OrdArith.add_assoc. *)
    (* refl. *)
  Qed.

  Definition myF (o0: Ord.t): Ord.t := ((alpha * kappa + c) ^ (o0 + 1))%ord.
  Definition myG (o0 m0: Ord.t): Ord.t := ((alpha * kappa + c) ^ (o0) * alpha * m0)%ord.
  Definition myH (o0: Ord.t): Ord.t := ((alpha * kappa + c) ^ (o0) * 3)%ord.

  (***
                         (myG o0 kappa + d <= myF o0)
  (AM: (m1 < m0)%ord) -> (myG o0 m1 + myH o0 + c <= myG o0 m0)%ord
  (O: (o1 < o0)%ord)  -> (myF o1 + e <= myH o0)%ord
   ***)

  Let NZERO: (Ord.O < alpha * kappa + c)%ord.
  Proof.
    unfold alpha.

    assert(T: (1 < f + 3 + d + e)%ord).
    { assert(U: (1 + 1 <= (Ord.from_nat 3))%ord).
      { rewrite <- OrdArith.add_from_nat. ss. eapply OrdArith.le_from_nat; et. }
      eapply Ord.lt_le_lt; cycle 1.
      { rewrite <- U. refl. }
      rewrite ! OrdArith.add_assoc.
      eapply Ord.lt_le_lt; cycle 1.
      { eapply OrdArith.add_base_r. }
      eapply OrdArith.add_lt_l.
      rewrite Ord.from_nat_S at 1.
      eapply Ord.lt_le_lt.
      { instantiate (1:=1%ord). rewrite Ord.from_nat_S. eapply Ord.S_pos. }
      { rewrite Ord.from_nat_S. eapply OrdArith.add_base_l. }
    }

    eapply Ord.lt_le_lt; cycle 1.
    { eapply OrdArith.add_base_l. }
    rewrite <- OrdArith.mult_1_r.
    eapply Ord.le_lt_lt; cycle 1.
    { instantiate (1:=((f + 3 + d + e) * 1)%ord).
      eapply OrdArith.lt_mult_r.
      - eauto with ord_kappa.
      - rewrite <- T. replace (Ord.from_nat 1) with (Ord.S Ord.O) by ss. eapply Ord.S_pos. }
    eapply mult_le_le.
    - eapply Ord.O_is_O.
    - refl.
  Qed.

  Global Program Instance myG_proper: Proper (Ord.le ==> Ord.le ==> Ord.le) (myG).
  Next Obligation.
    ii. unfold myG.
    rewrite <- H0.
    eapply mult_le_le; et; try refl.
    eapply mult_le_le; et; try refl.
    rewrite <- H. refl.
  Qed.

  Theorem my_thm1: forall o0, (myG o0 kappa + c <= myF o0)%ord.
  Proof.
    i. unfold myF, myG, myH.
    rewrite OrdArith.expn_add; et.
    rewrite OrdArith.expn_1_r; et.
    rewrite OrdArith.mult_dist.
    eapply add_le_le.
    - rewrite <- OrdArith.mult_assoc. refl.
    - rewrite <- (OrdArith.mult_1_l) at 1. eapply mult_le_le; try refl. eapply expn_pos.
    (* OrdArith.add *)
    (* OrdArith.mult *)
    (* OrdArith.expn *)
  Qed.

  Theorem my_thm3
          o0 o1
          (O: (o1 < o0)%ord)
    :
      (myF o1 + e <= myH o0)%ord
  .
  Proof.
    unfold myF, myG, myH.
    eapply add_one_lt in O.
    rewrite <- O.
    rewrite OrdArith.expn_add; et.
    rewrite OrdArith.expn_1_r; et.
    assert(T: (1 + 1 <= 3)%ord).
    { rewrite <- OrdArith.add_from_nat. ss. eapply OrdArith.le_from_nat; et. }
    rewrite <- T.
    rewrite OrdArith.mult_dist with (o2:=1).
    rewrite OrdArith.mult_1_r.
    eapply add_le_le; try refl.
    rewrite <- (OrdArith.mult_1_l) at 1.
    eapply mult_le_le.
    { eapply expn_pos. }
    rewrite <- alpha_e.
    etrans; [|eapply OrdArith.add_base_l].
    rewrite <- (OrdArith.mult_1_r) at 1.
    eapply mult_le_le; try refl.
    eapply Ord.lt_le.
    eauto with ord_kappa.
  Qed.

  Theorem my_thm2
          o0 m0 m1
          (AM: (m1 < m0)%ord)
    :
      (myG o0 m1 + f + myH o0 + d <= myG o0 m0)%ord
  .
  Proof.
    unfold myF, myG, myH.
    eapply add_one_lt in AM.
    rewrite <- AM.
    rewrite OrdArith.mult_dist.
    rewrite OrdArith.mult_1_r.
    rewrite OrdArith.add_assoc.
    rewrite OrdArith.add_assoc.
    eapply add_le_le; try refl.
    rewrite <- alpha_d at 3.
    rewrite OrdArith.mult_dist.
    rewrite OrdArith.mult_dist.
    rewrite <- OrdArith.add_assoc.
    eapply add_le_le; try refl; cycle 1.
    { rewrite <- (OrdArith.mult_1_l) at 1. eapply mult_le_le; try refl. eapply expn_pos. }
    eapply add_le_le; try refl; cycle 1.
    { rewrite <- (OrdArith.mult_1_l) at 1. eapply mult_le_le; try refl. eapply expn_pos. }
  Qed.

  End CONSTRUCTION.

End Construction.


Module MyParam <: PARAM.
  Definition d: Ord.t := 50%ord.
  Definition c: Ord.t := (d + 30)%ord.
  Definition e: Ord.t := 50%ord.
  Definition f: Ord.t := (d + 10)%ord.
End MyParam.

Module C := (Construction MyParam).












(* Lemma upcast_ty: forall T (v: T), Any.ty v↑ = T. admit "ez". Qed. *)
(* Lemma upcast_val: forall T (v: T), Any.val v↑ ~= v. admit "ez". Qed. *)

Lemma pair_downcast_lemma: forall T U (v0 v1: T) a (u: U), (Any.pair v0↑ a)↓ = Some (v1, u) -> v0 = v1 /\ a↓ = Some u.
Proof.
  admit "ez".
Qed.






Inductive opair: Type := mk_opair { ofst: Ord.t; osnd: Ord.t }.
(* Definition opair_lt: opair -> opair -> Prop := fun '(mk_opair x0 x1) '(mk_opair y0 y1) => (x0 < y0)%ord \/ (x0 == y0 /\ x1 < y1)%ord. *)
Inductive opair_lt: opair -> opair -> Prop :=
| intro_opair_lt
    x0 x1 y0 y1
    (LT: (x0 < y0)%ord \/ (x0 == y0 /\ x1 < y1)%ord)
  :
    opair_lt (mk_opair x0 x1) (mk_opair y0 y1)
.
Theorem wf_opair_lt: well_founded opair_lt.
Proof.
  ii. destruct a.
  revert osnd0. pattern ofst0. eapply well_founded_ind. { eapply Ord.lt_well_founded. } clear ofst0. intros ? IH0.
  intro. generalize dependent x. pattern osnd0. eapply well_founded_ind. { eapply Ord.lt_well_founded. } clear osnd0. intros ? IH1.
  econs. i. inv H. des.
  { eapply IH0; et. }
  { eapply IH1; et. i. eapply IH0; et. rewrite <- LT. ss. }
Qed.











Section CANCEL.

  (*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
  Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)



  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.

  Let sk: Sk.t := fold_right Sk.add Sk.unit (List.map SMod.sk mds).
  (* Let skenv: SkEnv.t := Sk.load_skenv sk. *)
  Let mss: list SModSem.t := (List.map ((flip SMod.get_modsem) sk) mds).
  Let sbtb: list (gname * fspecbody) := (List.flat_map (SModSem.fnsems) mss).
  Let stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb.

  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Let mds_mid: list Mod.t := List.map (SMod.to_mid stb) mds.



  Let W: Type := (r_state * p_state).
  (* Let wf: Ord.t -> W -> W -> Prop := top3. *)

  Opaque EventsL.interp_Es.

  Let ms_src: ModSemL.t := ModL.enclose (Mod.add_list mds_src).
  Let ms_mid: ModSemL.t := ModL.enclose (Mod.add_list mds_mid).

  Let p_src := ModSemL.prog ms_src.
  Let p_mid := ModSemL.prog ms_mid.

  Ltac _ord_step := eapply add_le_lt; [refl|eapply OrdArith.lt_from_nat; ss].

  Ltac _step tac :=
    match goal with
    (*** terminal cases ***)
    | [ |- gpaco5 _ _ _ _ _ _ _ (triggerUB >>= _) _ ] =>
      unfold triggerUB; mred; _step tac; ss; fail
    | [ |- gpaco5 _ _ _ _ _ _ _ (triggerNB >>= _) _ ] =>
      exfalso
    | [ |- gpaco5 _ _ _ _ _ _ _ _ (triggerUB >>= _) ] =>
      exfalso
    | [ |- gpaco5 _ _ _ _ _ _ _ _ (triggerNB >>= _) ] =>
      unfold triggerNB; mred; _step tac; ss; fail

    (*** assume/guarantee ***)
    | [ |- gpaco5 _ _ _ _ _ _ _ (assume ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco5 _ _ _ _ _ _ _ (guarantee ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar
    | [ |- gpaco5 _ _ _ _ _ _ _ _ (assume ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco5 _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar

    (*** default cases ***)
    | _ =>
      (gstep; tac; econs; auto; try (_ord_step);
       (*** some post-processing ***)
       i;
       try match goal with
           | [ |- (eq ==> _)%signature _ _ ] =>
             let v_src := fresh "v_src" in
             let v_tgt := fresh "v_tgt" in
             intros v_src v_tgt ?; subst v_tgt
           end)
    end
  .

  Ltac steps := repeat (mred; try _step ltac:(eapply simg_safe_spec); des_ifs_safe).
  Ltac steps_strong := repeat (mred; try (_step ltac:(idtac)); des_ifs_safe).

  Lemma stb_find_iff fn
    :
      is_some (alist_find fn stb) <-> is_some (find (fun fnsem => dec fn (fst fnsem)) (fnsems ms_mid)).
  Proof.
    admit "in stb <-> in fnsems".
  Qed.

  Let adequacy_type_aux__APC:
    forall at_most o0 mn
           st_src0 st_tgt0
    ,
      simg (fun _ '(st_tgt1, _) => st_tgt1 = st_tgt0)
           (C.myG o0 at_most + C.d)%ord (Ret (st_src0, tt))
           (EventsL.interp_Es p_mid (transl_all mn (interp_hCallE_mid stb (ord_pure o0) (_APC at_most))) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
    (* induction *)
    intros ? ?. remember (mk_opair o0 at_most) as fuel. move fuel at top. revert at_most o0 Heqfuel.
    pattern fuel. eapply well_founded_induction. { eapply wf_opair_lt. } clear fuel.
    intros fuel IH. i.

    rewrite unfold_APC. destruct st_tgt0 as [rst_tgt0 pst_tgt0]. steps.
    destruct x.
    { steps. }
    steps. destruct (alist_find s stb) eqn:EQ; ss.
    2: { steps. }
    destruct rst_tgt0 as [mrs_tgt0 [|frs_hd frs_tl]]; ss.
    { steps. destruct (Any.downcast t0); steps. }
    steps. destruct (Any.downcast t0); ss.
    2:{ steps. }
    steps. unfold unwrapU. des_ifs; cycle 1.
    { exfalso. hexploit (stb_find_iff s). rewrite EQ. rewrite Heq. clear. intuition. }
    unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
    unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
    rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
    rename Heq0 into INF. rename Heq into IN.
    rename x3 into md0. fold sk in INF. fold sk in INF.
    unfold fun_to_mid.
    steps. assert (f0.(fsb_fspec) = f).
    { admit "fspec table". }
    subst. rewrite Any.upcast_downcast. steps.
    guclo ordC_spec. econs.
    { eapply OrdArith.add_base_l. }
    guclo ordC_spec. econs.
    { eapply C.my_thm2; et. }
    guclo ordC_spec. econs.
    { rewrite OrdArith.add_assoc. refl. }
    rewrite idK_spec at 1.
    guclo bindC_spec. econs.
    { unfold APC. gstep. mred. eapply simg_chooseR; et; [_ord_step|]. i. steps.
      guclo ordC_spec. econs.
      { instantiate (1:=(C.myG x1 x3 + C.d)%ord).
        rewrite <- C.my_thm3; et.
        rewrite <- C.my_thm1; et.
        rewrite OrdArith.add_assoc.
        rewrite OrdArith.add_assoc.
        eapply add_le_le.
        - eapply Ord.lt_le in x4. rewrite <- x4. refl.
        - etrans; [|eapply OrdArith.add_base_l]. etrans; [|eapply OrdArith.add_base_l]. refl.
      }
      eapply IH; auto. econs. left. auto.
    }

    i. ss. destruct vret_tgt as [? []]. destruct vret_src as [? []]. ss. des; subst.
    unfold idK. unfold C.f.
    guclo ordC_spec. econs.
    { rewrite <- OrdArith.add_assoc. refl. }
    steps.
    guclo ordC_spec. econs.
    { eapply OrdArith.add_base_l. }
    { eapply IH; et. econs; et. right; split; et. refl. }
  Qed.

  Let adequacy_type_aux_APC:
    forall o0 st_src0 st_tgt0 mn
    ,
      simg (fun _ '(st_tgt1, _) => st_tgt1 = st_tgt0)
           (C.myF o0)%ord (Ret (st_src0, tt))
           (EventsL.interp_Es p_mid (transl_all mn (interp_hCallE_mid stb (ord_pure o0) APC)) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
    i. unfold APC.
    guclo ordC_spec. econs.
    { rewrite <- C.my_thm1. refl. }
    unfold C.c.
    guclo ordC_spec. econs.
    { rewrite <- OrdArith.add_assoc. refl. }
    steps.
    guclo ordC_spec. econs.
    { etrans; [|eapply OrdArith.add_base_l]. eapply add_le_le; [|refl].
      instantiate (1:=C.myG o0 x).
      eapply Ord.lt_le in x0. rewrite <- x0. refl. }
    gfinal. right.
    eapply adequacy_type_aux__APC.
  Qed.

  Lemma idK_spec2: forall E A B (a: A) (itr: itree E B), itr = Ret a >>= fun _ => itr. Proof. { i. ired. ss. } Qed.

  Definition formula (o0: ord): Ord.t :=
    match o0 with
    | ord_pure o0 => (10 + C.myF o0)%ord
    | ord_top => 100%ord
    end
  .

  Let wf: W -> W -> Prop := fun '(_, pst_src0) '(_, pst_tgt0) => pst_src0 = pst_tgt0.
  Let wf': forall {X}, (W * X)%type -> (W * X)%type -> Prop := (fun _ '(st_src0, rv_src) '(st_tgt0, rv_tgt) => wf st_src0 st_tgt0 /\ rv_src = rv_tgt).

  (*** TODO: remove redundancy with Hoareproof0 ***)
  Ltac resub :=
    repeat multimatch goal with
           | |- context[ITree.trigger ?e] =>
             match e with
             | subevent _ _ => idtac
             | _ => replace (ITree.trigger e) with (trigger e) by refl
             end
           | |- context[@subevent _ ?F ?prf _ (?e|)%sum] => replace (@subevent _ F prf _ (e|)%sum) with (@subevent _ F _ _ e) by refl
           | |- context[@subevent _ ?F ?prf _ (|?e)%sum] => replace (@subevent _ F prf _ (|e)%sum) with (@subevent _ F _ _ e) by refl
           end.

  Let adequacy_type_aux:
    forall
      o0
      A (body: itree _ A) st_src0 st_tgt0 mn
      (SIM: wf st_src0 st_tgt0)
    ,
      simg wf'
           100%ord
           (EventsL.interp_Es p_src (transl_all mn (interp_hCallE_src body)) st_src0)
           (EventsL.interp_Es p_mid (transl_all mn (interp_hCallE_mid stb o0 body)) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
    gcofix CIH. i. ides body.
    { steps. }
    { steps. gbase. eapply CIH; ss. }

    destruct e; cycle 1.
    { rewrite <- bind_trigger. resub. steps.
      destruct s; ss.
      { destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
        destruct p; ss.
        - steps. gbase. eapply CIH; ss; et.
        - steps. gbase. eapply CIH; ss; et.
      }
      { dependent destruction e.
        - steps_strong. exists x_tgt. steps. gbase. eapply CIH; et.
        - steps_strong. exists x_src. steps. gbase. eapply CIH; et.
        - steps_strong. gbase. eapply CIH; et.
      }
    }
    dependent destruction h.
    rewrite <- bind_trigger. resub.
    destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
    ired_both. destruct tbr.
    (* PURE *)
    { steps_strong.
      { admit "". }
      eexists. steps. destruct (alist_find fn stb) eqn:EQ.
      2: { steps. }
      steps. destruct (Any.downcast varg_src).
      2: { steps. }
      steps. destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]]; ss.
      { steps. }
      steps. clear x0. unfold unwrapU. des_ifs; cycle 1.
      { exfalso. hexploit (stb_find_iff fn). rewrite EQ. rewrite Heq. clear. intuition. }
      steps.

      guclo ordC_spec. econs.
      { instantiate (1:=_ + _). admit "". }
      rewrite idK_spec2 at 1.
      guclo bindC_spec. econs.
      {


  Let adequacy_type_aux:
    forall
      AA AR
      args
      o0
      body st_src0 st_tgt0 mn
      (SIM: wf st_src0 st_tgt0)
    ,
      simg wf'
           (formula o0 + 10)%ord
           (* (if is_pure o0 then trigger (Choose _) else (interp_Es p_src ((fun_to_src (AA:=AA) (AR:=AR) body) args↑) st0)) *)
           (EventsL.interp_Es p_src (transl_all mn (if is_pure o0 then trigger (Choose _) else ((fun_to_src (AA:=AA) (AR:=AR) body) args))) st_src0)
           (EventsL.interp_Es p_mid (transl_all mn ((fun_to_mid stb body) (Any.pair o0↑ args))) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
    gcofix CIH. i.
    unfold fun_to_src, fun_to_mid. steps. unfold unwrapN.
    destruct (Any.downcast (Any.pair (Any.upcast o0) args)) eqn:T; cycle 1.
    { steps. }
    destruct p.
    eapply pair_downcast_lemma in T. des; subst; ss. eapply Any.downcast_upcast in T0. des; subst.
    unfold body_to_src, cfun. steps. rewrite Any.upcast_downcast. ss. steps.
    destruct o; ss.
    - (*** PURE ***)
      seal_left.
      steps.
      unseal_left.
      erewrite idK_spec2 at 1.
      guclo ordC_spec. econs.
      { eapply OrdArith.add_base_l. }
      guclo bindC_spec.
      econs.
      { gfinal. right. eapply paco5_mon. { eapply adequacy_type_aux_APC. } ii; ss. }
      ii; ss. des_ifs. des_u.
      steps_strong. eexists. steps.
    -

      { admit "". }
      esplits; eauto.

      ste
 steps.
    - (*** IMPURE ***)
      steps. unfold body_to_mid.
      abstr (body a) itr. clear body a AA.

      guclo ordC_spec. econs.
      { instantiate (1:=(10 + 100)%ord). rewrite <- ! OrdArith.add_from_nat. ss. refl. }
      (* { instantiate (1:=(1 + 99)%ord). rewrite <- OrdArith.add_from_nat. ss. refl. } *)
      guclo bindC_spec. eapply bindR_intro with (RR:=wf'); cycle 1.
      { ii. subst. des_ifs. steps. r in SIM0. des; subst; ss. }

      revert_until CIH. gcofix CIH0. i.

      ides itr.
      { steps. }
      { steps. gbase. eapply CIH0; ss. }
      destruct e; cycle 1.
      {

        (*** TODO: remove redundancy with Hoareproof0 ***)
  Ltac resub :=
    repeat multimatch goal with
           | |- context[ITree.trigger ?e] =>
             match e with
             | subevent _ _ => idtac
             | _ => replace (ITree.trigger e) with (trigger e) by refl
             end
           | |- context[@subevent _ ?F ?prf _ (?e|)%sum] => replace (@subevent _ F prf _ (e|)%sum) with (@subevent _ F _ _ e) by refl
           | |- context[@subevent _ ?F ?prf _ (|?e)%sum] => replace (@subevent _ F prf _ (|e)%sum) with (@subevent _ F _ _ e) by refl
           end.
        rewrite <- bind_trigger. resub. steps.
        destruct s; ss.
        {
          destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
          destruct p; ss.
          - steps. instantiate (1:=100). gbase. eapply CIH0; ss; et.
          - steps. instantiate (1:=100). gbase. eapply CIH0; ss; et.
        }
        { dependent destruction e.
          - steps. unshelve esplits; et. instantiate (1:=100). steps. gbase. eapply CIH0; ss; et.
          - steps. unshelve esplits; et. instantiate (1:=100). steps. gbase. eapply CIH0; ss; et.
          - steps. unshelve esplits; et. instantiate (1:=100). steps. gbase. eapply CIH0; ss; et.
        }
      }
      dependent destruction h.
      rewrite <- bind_trigger. resub.
      Opaque fun_to_src fun_to_mid.

      destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
      ired_both.
      destruct tbr.
      + (*** PURE CALL ***)
        mred.
        seal_left.
        Ltac step := (mred; try _step; des_ifs_safe).
        step; try by eapply OrdArith.lt_from_nat.
        step; try by eapply OrdArith.lt_from_nat.
        unseal_left.
        step; try by eapply OrdArith.lt_from_nat.
        instantiate (1:=(120 + formula (ord_pure x) + 100)%ord).
        seal_left.

        steps.
        destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]]; ss.
        { unseal_left. steps. }
        steps.
        unfold unwrapU. des_ifs; cycle 1.
        { admit "unwrapN!!!!!!!!!!!!!!!!!!!!!!!!!!". }
        steps.
        unseal_left.
        unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
        unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
        rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
        rename Heq0 into INF. rename Heq into IN.
        rename x1 into md0. fold sk in INF. fold sk in INF.
        mred.
        guclo ordC_spec. econs.
        { instantiate (1:=(120 + (10 + C.myF x + 10))%ord).
          rewrite <- ! OrdArith.add_assoc. eapply add_le_le; try refl. eapply OrdArith.le_from_nat; ss. lia. }
        rename x into o1.
        rewrite <- bind_bind.
        rewrite <- bind_bind.
        guclo bindC_spec. econs.
        * (* guclo ordC_spec. econs. *)
          (* { eapply OrdArith.add_base_r. } *)
          (* gbase. eapply CIH; et. *)
          gbase. hexploit CIH; et.
          { instantiate (1:=(mrs_tgt0, ε :: frs_tgt_hd :: frs_tgt_tl, pst_tgt0)). instantiate (1:= (rst_src0, pst_tgt0)). ss. }
          intro T. instantiate (2:=(ord_pure o1)) in T. ss.
          mred.
          (*** applying reduction in "T" begin ***)
          (*** TODO: make prw "in" tactic ***)
          revert T. pose (fun (x: Prop) (y: Prop) => (x -> y)) as myf.
          match goal with | |- ?a -> ?b => replace (a -> b) with (myf a b) by refl end.
          try Red.prw ltac:(IRed._red_gen) 2 2 0.
          subst myf; cbn. intro T.
          (*** applying reduction in "T" end ***)
          eapply T.
        * ii. des_ifs. destruct p, p0; ss. des; subst.
          step; try by eapply OrdArith.lt_from_nat. steps.
          destruct r1; ss.
          des_ifs.
          { unfold triggerNB. steps; try by eapply OrdArith.lt_from_nat. (*** TODO: fix tactic, don't unfold triggerNB ***) }
          repeat (step; try by eapply OrdArith.lt_from_nat).
          guclo ordC_spec. econs.
          { instantiate (1:=100%ord). eapply OrdArith.le_from_nat; ss. lia. }
          gbase. eapply CIH0. ss.
      + (*** IMPURE CALL ***)
        mred.
        destruct rst_src0 as [mrs_src0 [|frs_src_hd frs_src_tl]]; ss.
        { admit "SOMEHOW". }
        mred. steps. instantiate (2:=(100 + (100 + 10) + 42)%ord). instantiate (1:=0%ord).
        guclo ordC_spec. econs. { rewrite OrdArith.add_O_r. refl. }
        destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]]; ss.
        { steps. }
        steps. unfold unwrapU at 2. des_ifs; cycle 1.
        { admit "unwrapN!!!!!!!!!!!!!!!!!!". }
        steps.
        unfold unwrapU. des_ifs; cycle 1.
        { steps. }
        steps.

        unfold ms_mid, mds_mid, SMod.to_mid in Heq. rewrite SMod.transl_fnsems in Heq.
        unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. des_sumbool; subst.
        rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq1. des; ss. des_ifs. ss; des; ss; clarify.
        rename Heq1 into INF. rename Heq into IN.
        rename x0 into md0. fold sk in INF. fold sk in INF.

        unfold ms_src, mds_src, SMod.to_src in Heq0. rewrite SMod.transl_fnsems in Heq0.
        unfold SMod.load_fnsems in Heq0. apply find_some in Heq0. des; ss. des_sumbool; subst.
        rewrite in_flat_map in Heq0. des; ss. rewrite in_flat_map in Heq1. des; ss. des_ifs. ss; des; ss; clarify.
        rename Heq1 into INF0. rename Heq0 into IN0.
        rename x0 into md1. fold sk in INF0. fold sk in INF0.

        assert(md0 = md1); subst.
        { admit "ez - uniqueness". }

        assert(f = f0); subst.
        { admit "ez - uniqueness". }

        guclo ordC_spec. econs.
        { eapply OrdArith.add_base_l. }
        guclo bindC_spec.
        econs.
        * hexploit CIH; et; cycle 1.
          { intro T. gbase. instantiate (3:=ord_top) in T. ss. eapply T. }
          { ss. }
        * ii; ss. des_ifs. steps. destruct p, p0; ss. des; subst.
          steps. destruct r1; ss. des_ifs.
          { unfold triggerNB. (step; try by eapply OrdArith.lt_from_nat). (*** TODO: fix tactic ***) }
          destruct r0; ss. des_ifs. { admit "somehow". } steps.
          instantiate (1:=100).
          gbase. eapply CIH0 ;ss.
  Unshelve.
    all: try (by econs; et).
    all: try (by exact Ord.O).
    all: ss.
  Unshelve.
    all: try (by exact unit).
  Qed.

  Theorem adequacy_type_m2s: Beh.of_program (ModL.compile (Mod.add_list mds_mid)) <1=
                             Beh.of_program (ModL.compile (Mod.add_list mds_src)).
  Proof.
    eapply adequacy_global.
    exists (100)%ord. ss.
    ginit.
    { eapply cpn5_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr. Local Opaque ModSemL.prog. ss.
    unfold ITree.map.
    unfold assume.
    steps.
    instantiate (1:=(10 + (100 + 10) + 42)%ord).
    esplits; et. { admit "ez - wf". } steps.
    Local Transparent ModSemL.prog.
    unfold ModSemL.prog at 4.
    unfold ModSemL.prog at 2.
    Local Opaque ModSemL.prog.
    ss. steps.
    (* Opaque ModSemL.initial_r_state. *)
    (* Opaque ModSemL.initial_p_state. *)
    fold ms_src. fold ms_mid.
    set (rs_src0 := initial_r_state ms_src) in *.
    set (rs_tgt0 := initial_r_state ms_mid) in *.
    assert(exists mrs_src0 hd_src tl_src, rs_src0 = (mrs_src0, hd_src :: tl_src)).
    { esplits. refl. }
    assert(exists mrs_tgt0 hd_tgt tl_tgt, rs_tgt0 = (mrs_tgt0, hd_tgt :: tl_tgt)).
    { esplits. refl. }
    des. clearbody rs_src0 rs_tgt0. subst.
    unfold unwrapU at 1. des_ifs; cycle 1.
    { steps. }
    unfold unwrapU. des_ifs; cycle 1.
    { admit "unwrapN!!!!!!!!!!". }


    unfold ms_mid, mds_mid, SMod.to_mid in Heq0. rewrite SMod.transl_fnsems in Heq0.
    unfold SMod.load_fnsems in Heq0. apply find_some in Heq0. des; ss. des_sumbool; subst.
    rewrite in_flat_map in Heq0. des; ss. rewrite in_flat_map in Heq2. des; ss. des_ifs. ss; des; ss; clarify. ss. subst.
    rename Heq2 into INF. rename Heq0 into IN.
    rename x into md0. fold sk in INF. fold sk in INF.

    unfold ms_src, mds_src, SMod.to_src in Heq. rewrite SMod.transl_fnsems in Heq.
    unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. destruct p; ss. des_sumbool; subst.
    rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
    rename Heq0 into INF0. rename Heq into IN0.
    rename x into md1. fold sk in INF0. fold sk in INF0.

    assert(md0 = md1); subst.
    { admit "ez - uniqueness". }
    assert(f = f0).
    { admit "ez - uniqueness". }
    subst.
    fold ms_src. fold ms_mid. fold p_src. fold p_mid.

    steps.

    match goal with
    | [ |- gpaco5 _ _ _ _ _ _ _ ?i_src _ ] => remember i_src as tmp
    end.
    replace (([]: list val)↑) with (Any.pair ord_top↑ ([]: list val)↑) by admit "TODO".
    subst tmp.

    guclo ordC_spec. econs.
    { eapply OrdArith.add_base_l. }
    guclo bindC_spec.
    econs.
    - hexploit adequacy_type_aux; cycle 1.
      { intro T. gfinal. right. instantiate (3:=ord_top) in T. ss. eapply T. }
      ss. unfold ms_src, ms_mid. unfold initial_p_state.
      apply func_ext. intro mn. unfold mds_src, mds_mid, SMod.to_src, SMod.to_mid.
      rewrite ! SMod.transl_initial_mrs. ss.
    - ii. rr in SIM. des_ifs. des; ss. subst. r in SIM. des_ifs. steps.
  Unshelve.
    all: ss.
    all: try (by exact Ord.O).
    all: try (by econs; et).
  Qed.

End CANCEL.
