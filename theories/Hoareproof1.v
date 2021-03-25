Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef.
Require Import SimSTS.
Require Import SimGlobal.
Require Import HoareDef.
From Ordinal Require Import Ordinal Arithmetic.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.
















Inductive _simg_safe (simg: forall R (RR: R -> R -> Prop), Ord.t -> (itree eventE R) -> (itree eventE R) -> Prop)
          {R} (RR: R -> R -> Prop) (i0: Ord.t): (itree eventE R) -> (itree eventE R) -> Prop :=
| simg_safe_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    _simg_safe simg RR i0 (Ret r_src) (Ret r_tgt)
| simg_safe_syscall
    i1 ktr_src0 ktr_tgt0 fn varg
    (SIM: (eq ==> simg _ RR i1)%signature ktr_src0 ktr_tgt0)
  :
    _simg_safe simg RR i0 (trigger (Syscall fn varg) >>= ktr_src0) (trigger (Syscall fn varg) >>= ktr_tgt0)



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
    | [ |- gpaco5 _ _ _ _ _ _ _ (assume ?P ;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco5 _ _ _ _ _ _ _ (guarantee ?P ;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar
    | [ |- gpaco5 _ _ _ _ _ _ _ _ (assume ?P ;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco5 _ _ _ _ _ _ _ _ (guarantee ?P ;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar

    (*** default cases ***)
    | _ =>
      (* gstep; eapply simg_safe_spec; econs; eauto; [|i] *)
      (gstep; eapply simg_safe_spec; econs; eauto; try (by eapply OrdArith.lt_from_nat; ss);
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
  Ltac steps_safe := repeat (mred; try _step; des_ifs_safe).













Section CANCEL.

  (*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
  Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)



  Context `{Σ: GRA.t}.

  Variable md_tgt: Mod.t.
  Let ms_tgt: ModSem.t := (Mod.get_modsem md_tgt (Sk.load_skenv md_tgt.(Mod.sk))).

  Variable sbtb: list (gname * fspecbody).
  Let stb: list (gname * fspec) := List.map (fun '(gn, fsb) => (gn, fsb_fspec fsb)) sbtb.

  Let md_mid: Mod.t := md_mid md_tgt sbtb.
  Let ms_mid: ModSem.t := ms_mid md_tgt sbtb.

  Let md_src: Mod.t := md_src md_tgt sbtb.
  Let ms_src: ModSem.t := ms_src md_tgt sbtb.

  Let W: Type := (r_state * p_state).
  (* Let wf: Ord.t -> W -> W -> Prop := top3. *)
  Let wf: W -> W -> Prop := eq.

  Definition c: Ord.t := 2%ord.
  Definition d: Ord.t := 2%ord.
  Definition _formula (o0: Ord.t): Ord.t := ((kappa * c + d) ^ (o0 + 1))%ord.
  Definition _formula2 (o0 at_most: Ord.t): Ord.t := ((kappa * c + d) ^ o0 * at_most)%ord.

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

  Program Instance expn_proper: Proper (Ord.eq ==> Ord.eq ==> Ord.eq) (OrdArith.expn).
  Next Obligation.
    ii.
    etrans.
    - eapply OrdArith.eq_expn_l; et.
    - eapply OrdArith.eq_expn_r; et.
  Qed.

  Program Instance add_proper: Proper (Ord.eq ==> Ord.eq ==> Ord.eq) (OrdArith.add).
  Next Obligation.
    ii.
    etrans.
    - eapply OrdArith.eq_add_l; et.
    - eapply OrdArith.eq_add_r; et.
  Qed.

  Program Instance mult_proper: Proper (Ord.eq ==> Ord.eq ==> Ord.eq) (OrdArith.mult).
  Next Obligation.
    ii.
    etrans.
    - eapply OrdArith.eq_mult_l; et.
    - eapply OrdArith.eq_mult_r; et.
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

  Theorem my_thm1: forall o0, (_formula2 o0 kappa + d < _formula o0)%ord.
  Proof.
    i. unfold _formula, _formula2.
    rewrite OrdArith.expn_add; cycle 1.
    { admit "ez". }
    rewrite OrdArith.expn_1_r; cycle 1.
    { admit "ez". }
    rewrite OrdArith.mult_dist.
    eapply Ord.le_lt_lt.
    { eapply OrdArith.le_add_l.
      instantiate (1:=((kappa * c + d) ^ o0 * (kappa * c))%ord).
      rewrite <- (OrdArith.mult_1_r kappa) at 2.
      eapply OrdArith.le_mult_r.
      eapply OrdArith.le_mult_r.
      replace (Ord.S Ord.O) with (Ord.from_nat 1); ss.
      eapply OrdArith.le_from_nat.
      lia.
    }
    TTTTTTTTTTtttTTTTTTTTTTTTTTTT
    eapply Ord.le_lt_lt.
    {
      ss.
      eapply Ord.from_nat
      unfold c.
      ss.
    OrdArith.lt_add_r
    OrdArith.le_add_r
    OrdArith.le_add_l

    OrdArith.add
    OrdArith.mult
    OrdArith.expn
  Qed.
  (* Definition formula (o0: ord): ord := *)
  (*   match o0 with *)
  (*   | ord_pure o0 => ord_pure (_formula o0) *)
  (*   | ord_top => ord_top *)
  (*   end *)
  (* . *)
  Definition formula (o0: ord): Ord.t :=
    match o0 with
    | ord_pure o0 => (_formula o0)
    | ord_top => 100%ord
    end
  .

  Opaque interp_Es.

  Let p_src := ModSem.prog ms_src.
  Let p_mid := ModSem.prog ms_mid.

  Let adequacy_type_aux_aux:
    forall o0
           at_most
           st0
    ,
      simg eq (formula o0) (interp_Es p_src (trigger (Choose _)) st0) (interp_Es p_mid (interp_hCallE_mid o0 (_APC at_most)) st0)
  .
  Proof.
    admit "".
  Qed.




  Let Any_pair_downcast: forall T0 T1 (v0: T0) (v1: T1), @Any.downcast (T0 * T1)%type (Any.pair v0↑ v1↑) = Some (v0, v1).
    { admit "ez - add this to Any.v ------------------". }
  Qed.

  Lemma interp_hCallE_mid_bind
        `{E -< Es} o0 R S (itr: itree (hCallE +' E) R) (ktr: ktree _ _ S)
    :
      interp_hCallE_mid o0 (itr >>= ktr) = (interp_hCallE_mid o0 itr) >>= (fun r => interp_hCallE_mid o0 (ktr r))
  .
  Proof. unfold interp_hCallE_mid. grind. Qed.

  Lemma interp_hCallE_mid_tau
        `{E -< Es} o0 R (itr: itree (hCallE +' E) R)
    :
      interp_hCallE_mid o0 (tau;; itr) = tau;; (interp_hCallE_mid o0 itr)
  .
  Proof. unfold interp_hCallE_mid. grind. Qed.

  Lemma interp_hCallE_mid_ret
        `{E -< Es} o0 R (r: R)
    :
      interp_hCallE_mid o0 (Ret r) = Ret r
  .
  Proof. unfold interp_hCallE_mid. grind. Qed.

  Lemma interp_hCallE_mid_eventE
        (* `{E -< Es} *)
        o0 R (e: eventE R)
    :
      interp_hCallE_mid (E:=pE +' eventE) o0 (trigger e) = r <- trigger e;; tau;; Ret r
  .
  Proof. unfold interp_hCallE_mid. rewrite interp_trigger. cbn. grind. Qed.

  Ltac hred :=
    repeat (try rewrite interp_hCallE_mid_bind; try rewrite interp_hCallE_mid_tau; try rewrite interp_hCallE_mid_ret; try rewrite interp_hCallE_mid_eventE
           ).

  Let adequacy_type_aux:
    forall
      AA AR
      (args: AA)
      o0
      body st0
    ,
      simg eq (formula o0) (interp_Es p_src ((fun_to_src (AA:=AA) (AR:=AR) body) args↑) st0)
           (interp_Es p_mid ((fun_to_mid body) (Any.pair o0↑ args↑)) st0)
  .
  Proof.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
    gcofix CIH. i.
    unfold fun_to_src, fun_to_mid. steps. rewrite Any_pair_downcast. ss. steps.
    unfold body_to_src, cfun. steps. rewrite Any.upcast_downcast. ss. steps.
    destruct o0.
    - (*** PURE ***)
      steps.
      Local Transparent APC. unfold APC. Local Opaque APC.
      hred. steps_safe.
      steps.
      rewrite interp_hCallE_mid_eventE.
      unfold interp_hCallE_mid. rewrite unfold_interp. steps.
      Esred.
      steps.
      move n at top.
      revert_until CIH.
      pattern n. eapply well_founded_induction. { eapply Ord.lt_well_founded. } clear n.
      intros nnn IH. i.
      i.
      eapply well_founded_ind.
      (* rename n into nnn. *)
      (* revert nnn. *)
      (* eapply ClassicalOrdinal.ClassicOrd.ind; i. *)
      +
    - (*** IMPURE ***)
    - steps.
    unfold interp_hCallE_src. unfold interp_hCallE_mid. rewrite  des_ifs. rewrite ! interp_trigger. steps.
  Qed.

  Let adequacy_type_aux:
    forall
      R
      ord_cur o0
      st0 tbr fn (args: R)
      (*     (he: hCallE Any.t) *)
    ,
      simg eq (formula o0) (interp_Es (ModSem.prog ms_src) (interp_hCallE_src (E:=pE +' eventE) (trigger (hCall tbr fn args↑))) st0)
           (interp_Es (ModSem.prog ms_mid) (interp_hCallE_mid (E:=pE +' eventE) ord_cur (trigger (hCall tbr fn (Any.pair o0↑ args↑)))) st0)
  .
  Proof.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
    gcofix CIH. i.
    unfold interp_hCallE_src. unfold interp_hCallE_mid. rewrite ! interp_trigger. steps.
  Qed.

  Let adequacy_type_aux:
    forall RT
           o0
           (* st_src0 st_tgt0 (SIM: wf st_src0 st_tgt0) *)
           st0
           (i0: itree (hCallE +' pE +' eventE) RT)
    ,
      simg (* (fun '((rs_src, v_src)) '((rs_tgt, v_tgt)) => wf rs_src rs_tgt /\ (v_src: RT) = v_tgt) *) eq (formula o0)
           (interp_Es (ModSem.prog ms_src) (interp_hCallE_src (E:=pE +' eventE) i0) st0)
           (interp_Es (ModSem.prog ms_mid) (interp_hCallE_mid (E:=pE +' eventE) o0 i0) st0)
  .
  Proof.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
    gcofix CIH. i; subst.
    unfold interp_hCallE_src.
    unfold interp_hCallE_mid.
    ides i0; try rewrite ! unfold_interp; cbn; mred.
    { steps. }
    { steps. gbase. eapply CIH. }
    destruct st0 as [rst0 pst0]; ss.
    destruct e; cycle 1.
    {
      destruct s; ss.
      {
        destruct p; ss.
        - steps. Esred. steps. gbase. eapply CIH.
        - steps. Esred. steps. gbase. eapply CIH.
      }
      { dependent destruction e.
        - steps. Esred. steps. esplits; eauto. steps. gbase. eapply CIH.
        - steps. Esred. steps. esplits; eauto. steps. gbase. eapply CIH.
        - steps. Esred. steps. esplits; eauto. steps. gbase. eapply CIH.
      }
    }
    dependent destruction h.
    cbn. steps.
    destruct tbr; cycle 1.
    - (*** IMPURE ***)
      destruct o0.
      { (*** can't be true ***)
        steps.
        { instantiate (1:=100). admit "ez". }
        unfold guarantee. steps.
      }
      steps. unfold unwrapU. des_ifs; steps.
      unfold guarantee. steps. unfold unwrapU. des_ifs; steps; cycle 1.
      { admit "ez - FINDF". }
      destruct rst0 as [mrs0 [|frs_hd frs_tl]]; ss.
      { seal_left. steps. }
      steps.
      guclo bindC_spec.
      admit "??????????????".
    - (*** PURE ***)

      (***
         We should execute APC <-
         We should call with ord_pure <-
         Current ord should be ord_pure <-
       ***)

      steps_safe.
      { instantiate (1:=100). admit "ez". }
      steps.
      eexists.
      seal_left.
      steps.
    rewrite unfold_interp.
    ss.
    seal_left.
TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT
  Qed.

  Theorem adequacy_type_m2s: Beh.of_program (Mod.interp md_mid) <1= Beh.of_program (Mod.interp md_src).
  Proof.
    eapply adequacy_global.
    exists (100)%ord. ss.
    ginit.
    { eapply cpn5_wcompat; eauto with paco. }
    unfold ModSem.initial_itr. Local Opaque ModSem.prog. ss.
    unfold ITree.map.
    unfold assume.
    steps.
    esplits; et. { admit "ez - wf". } steps.
    folder.
    set (st_src0 := ((ModSem.initial_r_state ms_src), (ModSem.initial_p_state ms_src))).
    set (st_mid0 := ((ModSem.initial_r_state ms_mid), (ModSem.initial_p_state ms_mid))).
    TTTTTTTTTTTTTTTTTT
    (* Local Opaque URA.add. *)
    assert(SIM: wf st_mid0 st_midmid0).
    { r. ss. esplits; ss; et. { admit "ez". } unfold ms_mid. unfold ModSem.initial_p_state. ss.
      apply func_ext. clear - Σ. i. rewrite ! find_map; ss. unfold compose. uo. unfold ms_tgt.
      des_ifs; ss; apply_all_once find_some; des; ss; des_sumbool; clarify.
      - destruct p0; ss. admit "ez - uniqueness of s".
      - eapply find_none in Heq0; et. ss. des_sumbool; ss.
      - eapply find_none in Heq1; et. des_ifs. ss. des_sumbool; ss.
    }
    unfold mrec.

    admit "migrate the proof from CompCertM-private".
  Qed.

End CANCEL.











Section EXPNS.
  Variable a: Ordinal.t.
  Hypothesis OMEGA: Ordinal.le Ordinal.omega a.
  Let NBOT: Ordinal.lt Ordinal.O a.
  Proof.
    eapply Ordinal.lt_le_lt; eauto. eapply Ordinal.lt_le_lt.
    { eapply Ordinal.S_lt. }
    eapply (Ordinal.join_upperbound Ordinal.from_nat 1).
  Qed.
  Lemma expn_positive o: Ordinal.lt Ordinal.O (Ordinal.expn a o).
  Proof.
    eapply Ordinal.lt_le_lt.
    { eapply Ordinal.S_lt. }
    eapply (Ordinal.orec_le_base (Ordinal.S Ordinal.O)
                                 (flip Ordinal.mult a)).
    i. eapply Ordinal.mult_le_l. auto.
  Qed.
  Lemma mult_base_l o: Ordinal.le o (Ordinal.mult o a).
  Proof.
    i. transitivity (Ordinal.mult o (Ordinal.from_nat 1)).
    { eapply Ordinal.mult_1_r. }
    eapply Ordinal.mult_le_r.
    eapply Ordinal.S_spec. eapply NBOT.
  Qed.
  Lemma expn_mon o0 o1 (LT: Ordinal.lt o0 o1):
    Ordinal.lt (Ordinal.expn a o0) (Ordinal.expn a o1).
  Proof.
    eapply (@Ordinal.lt_le_lt (Ordinal.expn a (Ordinal.S o0))).
    { eapply Ordinal.lt_eq_lt.
      { eapply Ordinal.orec_S.
        { apply mult_base_l. }
        { i. eapply Ordinal.mult_le_l. auto. }
      }
      { ss. eapply Ordinal.eq_lt_lt.
        { symmetry. eapply Ordinal.mult_1_r. }
        eapply Ordinal.mult_lt_r.
        { eapply Ordinal.lt_le_lt.
          { eapply Ordinal.S_lt. }
          transitivity Ordinal.omega; auto.
          eapply (Ordinal.join_upperbound Ordinal.from_nat 2).
        }
        eapply expn_positive.
      }
    }
    { eapply Ordinal.orec_le.
      { i. eapply Ordinal.mult_le_l. auto. }
      { eapply Ordinal.S_spec. auto. }
    }
  Qed.
  Fixpoint expns (l: list Ordinal.t): Ordinal.t :=
    match l with
    | [] => Ordinal.O
    | hd::tl => Ordinal.add (expns tl) (Ordinal.expn a hd)
    end.
  Lemma expns_positive hd: Ordinal.lt Ordinal.O (expns [hd]).
  Proof.
    ss. eapply Ordinal.lt_eq_lt.
    { eapply Ordinal.add_O_l. }
    eapply expn_positive.
  Qed.
  Lemma expns_app l0 l1: Ordinal.eq (expns (l0 ++ l1)) (Ordinal.add (expns l1) (expns l0)).
  Proof.
    induction l0; ss.
    { symmetry. eapply Ordinal.add_O_r. }
    etransitivity.
    { eapply Ordinal.add_eq_l. eapply IHl0. }
    eapply Ordinal.add_assoc.
  Qed.
  Lemma expns_ret hd tl: Ordinal.lt (expns tl) (expns (hd :: tl)).
  Proof.
    eapply Ordinal.lt_eq_lt.
    { eapply (expns_app [hd] tl). }
    eapply Ordinal.eq_lt_lt.
    { symmetry. eapply Ordinal.add_O_r. }
    eapply Ordinal.add_lt_r. eapply expns_positive.
  Qed.
  Fixpoint repeat X (n: nat) (x: X): list X :=
    match n with
    | O => []
    | S n' => x :: repeat n' x
    end.
  Lemma expns_call hd0 hd1 (LT: Ordinal.lt hd0 hd1) n:
    Ordinal.lt (expns (repeat n hd0)) (expns [hd1]).
  Proof.
    ss. eapply Ordinal.lt_eq_lt.
    { eapply Ordinal.add_O_l. }
    eapply (@Ordinal.lt_le_lt (Ordinal.expn a (Ordinal.S hd0))).
    2: {
      eapply Ordinal.orec_le.
      { i. eapply Ordinal.mult_le_l. auto. }
      { eapply Ordinal.S_spec. auto. }
    }
    eapply Ordinal.lt_eq_lt.
    { eapply Ordinal.orec_S.
      { apply mult_base_l. }
      { i. eapply Ordinal.mult_le_l. auto. }
    }
    ss. eapply Ordinal.lt_le_lt.
    2: {
      instantiate (1:=Ordinal.mult (Ordinal.expn a hd0) Ordinal.omega).
      eapply Ordinal.mult_le_r. auto.
    }
    eapply Ordinal.le_lt_lt.
    2: {
      eapply Ordinal.mult_lt_r.
      { instantiate (1:=Ordinal.from_nat n).
        eapply Ordinal.lt_le_lt.
        { eapply Ordinal.S_lt. }
        { eapply (Ordinal.join_upperbound Ordinal.from_nat (S n)). }
      }
      { eapply expn_positive. }
    }
    Local Opaque Ordinal.mult.
    induction n; ss.
    { eapply Ordinal.mult_O_r. }
    { etransitivity.
      { eapply Ordinal.add_le_l. eapply IHn. }
      { eapply Ordinal.mult_S. }
    }
  Qed.
  Lemma expns_call_list hd0 hd1 tl (LT: Ordinal.lt hd0 hd1) n:
    Ordinal.lt (expns ((repeat n hd0) ++ tl)) (expns (hd1 :: tl)).
  Proof.
    eapply Ordinal.eq_lt_lt.
    { eapply expns_app. }
    eapply Ordinal.lt_eq_lt.
    { eapply (expns_app [hd1] tl). }
    eapply Ordinal.add_lt_r. eapply expns_call. auto.
  Qed.
End EXPNS.
