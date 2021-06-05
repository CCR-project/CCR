Require Import MemClient0 MemClient1 HoareDef SimModSem.
Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import TODOYJ.
Require Import HTactics Logic IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section AUX.

  Context `{Σ: GRA.t}.

  Lemma APCK_start_clo
        (at_most: Ord.t) (n1: Ord.t)
        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt

        (ATMOST: (at_most < kappa)%ord)
        (FUEL: (n1 + 5 < n0)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                       (mr_src0, mp_src0, fr_src0,
                       (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK at_most))) >>= k_src)
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
              (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt APCK)) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    unfold APCK. steps. force_l.
    exists at_most. ired_l.  _step; [by eauto with ord_step|]. steps; [by eauto with ord_step|].
    unfold guarantee. ired_both. force_l. esplits; et.
    ired_both. _step; [by eauto with ord_step|]. steps; [by eauto with ord_step|]. ss.
    guclo lordC_spec. econs; et. rewrite OrdArith.add_O_r. refl.
  Qed.

  Lemma APCK_step_clo
        (fn: gname) (next: Ord.t) (n1: Ord.t)

        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (at_most: Ord.t)
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt

        (FUEL: (n1 + 11 < n0)%ord)
        (ftsp: ftspec unit unit)
        (FIND: alist_find fn stb = Some (KModSem.disclose ftsp))
        (NEXT: (next < at_most)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                      (mr_src0, mp_src0, fr_src0,
                       (HoareCall true o (KModSem.disclose ftsp) fn (inl tt));;;
                                 tau;; tau;; (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK next)))
                                               >>= k_src)
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
             (mr_src0, mp_src0, fr_src0, (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK at_most)))
                                           >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    rewrite unfold_APCK. steps. force_l. exists false. ired_both.
    _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l. esplits; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l. esplits; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    rewrite FIND. ired_both. rewrite Any.upcast_downcast. ired_both.
    guclo lordC_spec. econs; et. { rewrite OrdArith.add_O_r. refl. }
    match goal with
    | [SIM: gpaco6 _ _ _ _ _ _ _ _ ?i0 _ |- gpaco6 _ _ _ _ _ _ _ _ ?i1 _] =>
      replace i1 with i0; auto
    end.
    f_equal. grind. ired_both. grind. ired_both. grind.
  Qed.

  Lemma APCK_stop_clo
        (n1: Ord.t)

        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (at_most: Ord.t)
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt

        (FUEL: (n1 + 2 < n0)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                      (mr_src0, mp_src0, fr_src0, k_src ())
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
              (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK at_most))) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    rewrite unfold_APCK. steps. force_l. exists true.
    ired_both; _step; [by eauto with ord_step|].
    ired_both; _step; [by eauto with ord_step|].
    steps.
    guclo lordC_spec. econs; et. { rewrite OrdArith.add_O_r. refl. }
  Qed.

End AUX.

Ltac kstart _at_most :=
  eapply (APCK_start_clo) with (at_most := _at_most);
  [eauto with ord_kappa|
   (try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
  ]
.

Ltac kstep _fn :=
  eapply (@APCK_step_clo _ _fn);
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
   (try by (stb_tac; refl))|
   (eapply OrdArith.lt_from_nat; eapply Nat.lt_succ_diag_r)|
  ].

Ltac kcatch :=
  match goal with
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?fn _) >>= _)) ] =>
    kstep fn
  end.

Ltac kstop :=
  eapply APCK_stop_clo;
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|].



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  (* Let wf: W -> Prop := top1. *)
  Let wf: W -> Prop := @mk_wf _ unit (fun _ _ _ => ⌜True⌝%I) (fun _ _ _ => ⌜True⌝%I).

  (* Definition __hide_mark A (a : A) : A := a. *)
  (* Lemma intro_hide_mark: forall A (a: A), a = __hide_mark a. refl. Qed. *)

  (* Ltac hide_k :=  *)
  (*   match goal with *)
  (*   | [ |- (gpaco6 _ _ _ _ _ _ _ _ (_, ?isrc >>= ?ksrc) (_, ?itgt >>= ?ktgt)) ] => *)
  (*     erewrite intro_hide_mark with (a:=ksrc); *)
  (*     erewrite intro_hide_mark with (a:=ktgt); *)
  (*     let name0 := fresh "__KSRC__" in set (__hide_mark ksrc) as name0; move name0 at top; *)
  (*     let name0 := fresh "__KTGT__" in set (__hide_mark ktgt) as name0; move name0 at top *)
  (*   end. *)

  (* Ltac unhide_k := *)
  (*   do 2 match goal with *)
  (*   | [ H := __hide_mark _ |- _ ] => subst H *)
  (*   end; *)
  (*   rewrite <- ! intro_hide_mark *)
  (* . *)

  Theorem sim_modsem: ModSemPair.sim (MemClient1.ClientSem (UnknownStb ++ ClientStb ++ MemStb)) MemClient0.ClientSem.
  Proof.
    econstructor 1 with (wf:=wf); ss; et; swap 2 3.
    { econs; ss.
      - eapply to_semantic; cycle 1. { eapply URA.wf_unit. } iIntros "H". iPureIntro. ss.
      - eapply to_semantic; cycle 1. { eapply URA.wf_unit. } iIntros "H". iPureIntro. ss.
    }
    econs; ss.
    { unfold clientF. init. harg. destruct varg_src.
      { ss. des_ifs; mDesAll; ss. }
      destruct x; mDesAll; ss. des; subst.
      unfold clientBody. steps. kstart 2.

      kcatch. hcall _ (Some _) _ with ""; ss; et.
      { iModIntro. iSplitR; ss. iPureIntro. esplits; et. instantiate (1:=1%nat). ss. }
      { ss. }
      steps. mDesAll. subst. rewrite Any.upcast_downcast in *. clarify.

      kcatch. hcall _ (Some (_, _, _)) _ with "A"; ss; et.
      { iModIntro. iSplitR; ss. iSplitL; ss.
        - iExists _. iSplitL; ss. iSplitR; ss.
        - ss.
      }
      { ss. }
      steps. kstop.

      force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
      hcall _ _ _ with ""; ss; et.
      { iModIntro. iSplitR; ss. iPureIntro. esplits; et. rewrite Any.upcast_downcast. ss. }
      { ss. }
      steps. mDesAll. subst.

      kstart 1.
      kcatch. hcall _ (Some (_, _, _)) _ with "POST"; ss; et.
      { iModIntro. iSplitR; ss. iSplitL; ss.
        - iSplitL; ss. iSplitR; ss.
        - ss.
      }
      { ss. }
      steps. kstop. mDesAll. subst. rewrite Any.upcast_downcast in *. clarify. steps.

      hret _; ss.
    }
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Theorem correct: ModPair.sim (MemClient1.Client (fun _ => (UnknownStb ++ ClientStb ++ MemStb)))
                               MemClient0.Client.
  Proof.
    econs; ss.
    { ii. eapply adequacy_lift. eapply sim_modsem. }
    ii; ss. repeat (econs; ss).
  Qed.

End SIMMOD.
