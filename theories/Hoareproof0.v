Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Ordinal ClassicalOrdinal.
Require Import Any.
Require Import HoareDef.
Require Import SimSTS.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.










Section CANCEL.

  (*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
  Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)



  Context `{Σ: GRA.t}.
  Opaque GRA.to_URA.

  Variable md_tgt: Mod.t.
  Let ms_tgt: ModSem.t := (Mod.get_modsem md_tgt (Sk.load_skenv md_tgt.(Mod.sk))).

  Variable sbtb: list (gname * fspecbody).
  Let stb: list (gname * fspec) := List.map (fun '(gn, fsb) => (gn, fsb_fspec fsb)) sbtb.
  Hypothesis WTY: ms_tgt.(ModSem.fnsems) = List.map (fun '(fn, sb) => (fn, fun_to_tgt stb fn sb)) sbtb.
  Let md_mid: Mod.t := md_mid md_tgt sbtb.
  Let ms_mid: ModSem.t := ms_mid md_tgt sbtb.

  Let W: Type := (r_state * p_state).
  Let rsum: r_state -> Σ :=
    fun '(mrs_tgt, frs_tgt) => (URA.add (fold_left URA.add (List.map (mrs_tgt <*> fst) ms_tgt.(ModSem.initial_mrs)) ε)
                                        (fold_left URA.add frs_tgt ε)).
  Let wf: W -> W -> Prop :=
    fun '((mrs_src, frs_src), mps_src) '((mrs_tgt, frs_tgt), mps_tgt) =>
      (<<LEN: List.length frs_src = List.length frs_tgt>>) /\
      (<<NNIL: frs_src <> []>>) /\
      (<<WFTGT: URA.wf (rsum (mrs_tgt, frs_tgt))>>) /\
      (<<PHYS: mps_src = mps_tgt>>)
  .
  Local Opaque rsum.

  Let WF0: List.map fst sbtb = List.map fst stb.
  Proof. unfold stb. rewrite List.map_map. apply List.map_ext. i. des_ifs. Qed.
  Hypothesis WF1: Forall (fun '(_, sp) => In sp.(mn) (List.map fst ms_tgt.(ModSem.initial_mrs))) stb.

  Require Import SimGlobal.


  (* Ltac grind := repeat (f_equiv; try apply func_ext; ii; try (des_ifs; check_safe)). *)

  (* Ltac igo := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r; try rewrite bind_tau; *)
  (*                     try rewrite interp_vis; *)
  (*                     try rewrite interp_ret; *)
  (*                     try rewrite interp_tau *)
  (*                     (* try rewrite interp_trigger *) *)
  (*                    ). *)
  Infix "⋅" := URA.add (at level 50, left associativity).
  Notation "(⋅)" := URA.add (only parsing).

  Let adequacy_type_aux:
    forall (R: Type) (RR: R -> R -> Prop) RT (TY: R = (r_state * p_state * RT)%type)
           (REL: RR ~= (fun '((rs_src, v_src)) '((rs_tgt, v_tgt)) => wf rs_src rs_tgt /\ (v_src: RT) = v_tgt))
           (* (REL: RR ~= (fun '((rs_src, v_src)) '((rs_tgt, v_tgt)) => wf rs_src rs_tgt /\ exists (o: ord), (v_src: Any_mid) = Any.pair o↑ (v_tgt: Any_src))) *)
           st_src0 st_tgt0 (SIM: wf st_src0 st_tgt0) (i0: itree (hCallE +' pE +' eventE) RT)
           i_src i_tgt mn cur
           (SRC: i_src ~= (interp_Es (ModSem.prog ms_mid) (interp_hCallE_mid (E:=pE +' eventE) cur i0) st_src0))
           (TGT: i_tgt ~= (interp_Es (ModSem.prog ms_tgt) (interp_hCallE_tgt (E:=pE +' eventE) stb mn cur i0) st_tgt0))
    ,
    (* sim (Mod.interp md_src) (Mod.interp md_tgt) lt 100%nat *)
    (*     (x <- (interp_Es p_src (interp_hCallE_src (trigger ce)) st_src0);; Ret (snd x)) *)
    (*     (x <- (interp_Es p_tgt (interp_hCallE_tgt stb (trigger ce)) st_tgt0);; Ret (snd x)) *)
    simg RR (Ordinal.from_nat 100%nat) i_src i_tgt
  .
  Proof.
    i. ginit.
    { eapply cpn5_wcompat; eauto with paco. }
    (* remember (` x : ModSem.r_state * R <- interp_Es p_src (interp_hCallE_src (trigger ce)) st_src0;; Ret (snd x)) as tmp. *)
    revert_until R. revert R.
    unfold Relation_Definitions.relation.
    gcofix CIH. i; subst.
    (* intros ? ?. *)
    (* pcofix CIH. i. *)
    unfold interp_hCallE_mid.
    unfold interp_hCallE_tgt.
    ides i0; try rewrite ! unfold_interp; cbn; mred.
    { steps. }
    { steps. gbase. eapply CIH; [..|M]; Mskip et.
      { refl. }
      { instantiate (1:=mn). fold (interp_hCallE_tgt stb mn). refl. }
    }
    destruct e; cycle 1.
    {
      Opaque interp_Es.
      destruct s; ss.
      {
        destruct st_src0 as [rst_src0 pst_src0], st_tgt0 as [rst_tgt0 pst_tgt0]; ss. des_ifs. des; clarify.
        destruct p; ss.
        - steps. gbase. eapply CIH; [refl|ss|..]; cycle 1.
          { unfold interp_hCallE_src. refl. }
          { unfold interp_hCallE_tgt. refl. }
          ss.
        - steps. gbase. eapply CIH; [refl|ss|..]; cycle 1.
          { unfold interp_hCallE_src. refl. }
          { unfold interp_hCallE_tgt. refl. }
          ss.
      }
      { dependent destruction e.
        - steps. esplits; eauto. steps.
          gbase. eapply CIH; [..|M]; Mskip et.
          { refl. }
          { instantiate (2:=mn). fold (interp_hCallE_tgt stb mn). refl. }
        - steps. esplits; eauto. steps.
          gbase. eapply CIH; [..|M]; Mskip et.
          { refl. }
          { instantiate (1:=mn). fold (interp_hCallE_tgt stb mn). refl. }
        - steps.
          gbase. eapply CIH; [..|M]; Mskip et.
          { refl. }
          { instantiate (1:=mn). fold (interp_hCallE_tgt stb mn). refl. }
      }
    }
    dependent destruction h.
    set (ModSem.prog ms_mid) as p_mid in *.
    set (ModSem.prog ms_tgt) as p_tgt in *.
    Local Opaque GRA.to_URA.
    ss.
    seal_left.

    (* Ltac hide_left := *)
    (*   match goal with *)
    (*   | [ |- gpaco5 _ _ _ _ _ _ _ ?i_src ?i_tgt ] => let name := fresh "HIDDEN" in remember i_src as HIDDEN *)
    (*   end. *)
    (* hide_left. *)
    steps.
    destruct (find (fun '(_fn, _) => dec fn _fn) stb) eqn:FINDFT; cycle 1.
    { steps. }
    (* unfold ModSem.prog at 2. steps. *)
    unfold HoareCall.
    steps. unfold put, guarantee. steps.
    destruct st_tgt0 as [rst_tgt0 pst_tgt0]. destruct st_src0 as [rst_src0 pst_src0].
    Opaque interp_Es. (*** TODO: move to ModSem ***)
    destruct (varg_src↓) eqn:CAST; cycle 1.
    { steps. }
    steps. unfold handle_rE. destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]] eqn:T; ss.
    { rr in SIM. des_ifs_safe. des; ss. destruct l; ss. }
    steps. unfold guarantee. (*** TODO: remove: unfold guarantee ***)
    (* do 2 (mred; try _step; des_ifs_safe). *)
    (* unseal_left. *)
    (* seal_right. _step. exists (x2↑). mred. unseal_right. *)
    (* _step. instantiate (1:=Ordinal.from_nat 300). *)
    (* assert(idK_spec2: forall E A B (a: A) (itr: itree E B), itr = Ret a >>= fun _ => itr). *)
    (* { i. ired. ss. } *)
    (* match goal with *)
    (* | [ |- gpaco5 _ _ _ _ _ _ _ ?i_src ?i_tgt ] => erewrite idK_spec2 with (itr := i_tgt) *)
    (* end. *)
    (* guclo bindC_spec. *)
    (* replace (Ordinal.from_nat 80) with (Ordinal.add (Ordinal.from_nat 70) (Ordinal.from_nat 10)) by admit "ez". *)
    (* eapply bindR_intro with (RR:=(fun '((rs_src, v_src)) '((rs_tgt, v_tgt)) => wf rs_src rs_tgt /\ (v_src: ord) = v_tgt)). *)
    (* { des_ifs. *)
    (*   - instantiate(1:=(c1, l, pst_src0, ord_top)). steps. esplits; eauto. steps. des; ss. esplits; ss; et. *)
    (*   - steps. *)
    (* } *)
    (* i; subst. *)
    (* destruct vret_tgt as [[[mrs0 frs0] mps0] ord_cur]. *)
    unfold discard. steps.
    unfold guarantee. steps.
    unseal_left.
    destruct tbr.
    { steps. esplits; eauto. steps. esplits; eauto. steps. unfold unwrapU.
      destruct (find (fun fnsem => dec fn (fst fnsem)) (List.map (fun '(fn0, sb) => (fn0, fun_to_mid (fsb_body sb))) sbtb)) eqn:FINDFS; cycle 1.
      { steps. }
      destruct (find (fun fnsem => dec fn (fst fnsem)) (ModSem.fnsems ms_tgt)) eqn:FINDFT0; cycle 1.
      { steps.
        rewrite WTY in *. ss. clear - FINDFS FINDFT0.
        rewrite find_map in *. uo. des_ifs.
        apply_all_once find_some. des.
        eapply find_none in Heq0; eauto.
        unfold compose in *. des_ifs. ss. des_sumbool. ss.
      }
      mred. des_ifs. mred. destruct l; ss.
      { des; ss. }
      mred. steps.
      rename i into i_src.
      rename i0 into i_tgt.
      guclo bindC_spec.
      instantiate (2:=Ordinal.from_nat 400).
      replace (Ordinal.from_nat 400) with
          (Ordinal.add (Ordinal.from_nat 200) (Ordinal.from_nat 200)); cycle 1.
      { admit "ez". }
      rename f into fs.
      econs.
      - instantiate (2:= fun '((((mrs_src, frs_src), mps_src), vret_src): (r_state * p_state * Any_src))
                             '((((mrs_tgt, frs_tgt), mps_tgt), vret_tgt): (r_state * p_state * Any_tgt)) =>
                           exists (rret: Σ) (vret_src': fs.(AR)),
                             (<<ST: (List.length frs_src) = (List.length frs_tgt) /\
                                    frs_src <> [] /\
                                    URA.wf (rsum (mrs_tgt, rret :: frs_tgt))>>) /\
                             (* (<<VAL: vret_src = vret_tgt>>) /\ *)
                             (<<CAST: vret_src↓ = Some vret_src'>>) /\
                             (<<POST: fs.(postcond) x2 vret_src' vret_tgt rret>>) /\
                             (<<PHYS: mps_src = mps_tgt>>)
                    ).
        apply find_some in FINDFT0. des.
        apply find_some in FINDFS. des. ss. des_sumbool. clarify.
        rewrite WTY in *. fold Any_src in FINDFS. fold Any_tgt in FINDFT0. rewrite in_map_iff in *. des. des_ifs.
        assert(f0 = f) by admit "ez - uniqueness of idx. Add this as an hypothesis". subst.
        assert(fs = f). {
          rename f into fss.
          apply find_some in FINDFT. des. des_sumbool. clarify.
          unfold stb in FINDFT. rewrite in_map_iff in *. des. des_ifs.
          admit "ez - uniqueness of idx. Add this as an hypothesis".
        } subst.
        fold Any_tgt in x3.
        unfold fun_to_src, fun_to_tgt. des_ifs. unfold HoareFun.
        rename x3 into PRECOND. rename x0 into rarg.
        steps. exists a.
        steps. esplits; et. steps. exists rarg.
        steps. unfold forge, checkWf. steps. unfold assume, guarantee.
        steps. unshelve esplits; eauto.
        { clear - WFTGT x. rewrite URA.unit_idl. rewrite URA.add_assoc in x.
          r in x. specialize (x URA.unit). rewrite ! URA.unit_id in x.
          unfold update. des_ifs.
          - eapply URA.wf_mon. eapply x. admit "ez - WFTGT".
          - admit "ez - c1 contains both (c1 mn0) and (c1 (mn fs)).".
        }
        steps. esplits; eauto. steps. unfold cfun. steps. unshelve esplits; eauto. steps.
        unfold fun_to_mid. instantiate (1:=x4).
        assert(CAST0: varg_src = Any.upcast a).
        { erewrite Any.downcast_upcast; et. }
        rewrite CAST0.
        assert(Any_pair_downcast: forall T0 T1 (v0: T0) (v1: T1), @Any.downcast (T0 * T1)%type (Any.pair v0↑ v1↑) = Some (v0, v1)).
        { admit "ez - add this to Any.v ------------------". }
        rewrite Any_pair_downcast.
        steps. destruct x4; ss; cycle 1.
        { exfalso. exploit x7; ii; ss. }
        steps.
        guclo bindC_spec.
        replace (Ordinal.from_nat 168) with (Ordinal.add (Ordinal.from_nat 68) (Ordinal.from_nat 100)); cycle 1.
        { admit "ez - ordinal nat add". }
        econs.
        + gbase. eapply CIH; et; try refl. rr. esplits; ss; et. rewrite URA.unit_idl. clear - WFTGT x. admit "ez".
        + ii. ss. des_ifs_safe. des; ss. clarify. des_u.
          steps. esplits; eauto. steps. unfold put. steps. destruct p0; ss. steps.
          unfold handle_rE. destruct r0; ss. destruct l0; ss.
          { steps. }
          steps.
          unfold guarantee.
          steps.
          unfold discard.
          steps.
          unfold guarantee. steps. r in SIM. des; ss. rewrite Any.upcast_downcast. esplits; ss; eauto.
          clear - x3 WFTGT0.
          admit "ez".
      - ii. ss. des_ifs. des. (* rr in SIM0. des; ss. unfold RelationPairs.RelCompFun in *. ss. *)
        (* r in SIM0. des_ifs. des; ss. *)
        steps. clear_tac. instantiate (1:=125).
        unfold checkWf, assume; steps.
        des_ifs; ss.
        { steps. }
        steps.
        unshelve esplits; eauto.
        { clear - ST1. admit "ez". }
        steps. esplits; eauto.
        unfold forge; steps. esplits; et.
        steps. unshelve esplits; eauto. steps.
        fold interp_hCallE_src. fold (interp_hCallE_tgt stb mn).
        gbase. eapply CIH; [refl|ss|..]; cycle 1.
        { refl. }
        { unfold interp_hCallE_tgt. erewrite Any.downcast_upcast; et. }
        rr. esplits; et. { destruct l2; ss. } clear - ST1. admit "ez".
    }
    { des. clear x7. exploit x8; et. i; clarify. clear x8.
      steps. esplits; eauto. steps. esplits; eauto. steps. unfold unwrapU.
      destruct (find (fun fnsem => dec fn (fst fnsem)) (List.map (fun '(fn0, sb) => (fn0, fun_to_mid (fsb_body sb))) sbtb)) eqn:FINDFS; cycle 1.
      { steps. }
      destruct (find (fun fnsem => dec fn (fst fnsem)) (ModSem.fnsems ms_tgt)) eqn:FINDFT0; cycle 1.
      { steps.
        rewrite WTY in *. ss. clear - FINDFS FINDFT0.
        rewrite find_map in *. uo. des_ifs.
        apply_all_once find_some. des.
        eapply find_none in Heq0; eauto.
        unfold compose in *. des_ifs. ss. des_sumbool. ss.
      }
      mred. des_ifs. mred. destruct l; ss.
      mred. steps.
      rename i into i_src.
      rename i0 into i_tgt.
      guclo bindC_spec.
      instantiate (1:=Ordinal.from_nat 400).
      replace (Ordinal.from_nat 400) with
          (Ordinal.add (Ordinal.from_nat 200) (Ordinal.from_nat 200)); cycle 1.
      { admit "ez". }
      rename f into fs.
      econs.
      - instantiate (1:= fun '((((mrs_src, frs_src), mps_src), vret_src): (r_state * p_state * Any_src))
                             '((((mrs_tgt, frs_tgt), mps_tgt), vret_tgt): (r_state * p_state * Any_tgt)) =>
                           exists (rret: Σ) (vret_src': fs.(AR)),
                             (<<ST: (List.length frs_src) = (List.length frs_tgt) /\
                                    frs_src <> [] /\
                                    URA.wf (rsum (mrs_tgt, rret :: frs_tgt))>>) /\
                             (* (<<VAL: vret_src = vret_tgt>>) /\ *)
                             (<<CAST: vret_src↓ = Some vret_src'>>) /\
                             (<<POST: fs.(postcond) x2 vret_src' vret_tgt rret>>) /\
                             (<<PHYS: mps_src = mps_tgt>>)
                    ).
        apply find_some in FINDFT0. des.
        apply find_some in FINDFS. des. ss. des_sumbool. clarify.
        rewrite WTY in *. fold Any_src in FINDFS. fold Any_tgt in FINDFT0. rewrite in_map_iff in *. des. des_ifs.
        assert(f0 = f) by admit "ez - uniqueness of idx. Add this as an hypothesis". subst.
        assert(fs = f). {
          rename f into fss.
          apply find_some in FINDFT. des. des_sumbool. clarify.
          unfold stb in FINDFT. rewrite in_map_iff in *. des. des_ifs.
          admit "ez - uniqueness of idx. Add this as an hypothesis".
        } subst.
        fold Any_tgt in x3.
        unfold fun_to_src, fun_to_tgt. des_ifs. unfold HoareFun.
        rename x3 into PRECOND. rename x0 into rarg.
        steps. exists a.
        steps. esplits; et. steps. exists rarg.
        steps. unfold forge, checkWf. steps. unfold assume, guarantee.
        steps. unshelve esplits; eauto.
        { clear - WFTGT x. rewrite URA.unit_idl. rewrite URA.add_assoc in x.
          r in x. specialize (x URA.unit). rewrite ! URA.unit_id in x.
          unfold update. des_ifs.
          - eapply URA.wf_mon. eapply x. admit "ez - WFTGT".
          - admit "ez - c1 contains both (c1 mn0) and (c1 (mn fs)).".
        }
        steps. esplits; eauto. steps. unfold cfun. steps. unshelve esplits; eauto. steps.
        unfold fun_to_mid.
        assert(CAST0: varg_src = Any.upcast a).
        { erewrite Any.downcast_upcast; et. }
        rewrite CAST0.
        assert(Any_pair_downcast: forall T0 T1 (v0: T0) (v1: T1), @Any.downcast (T0 * T1)%type (Any.pair v0↑ v1↑) = Some (v0, v1)).
        { admit "ez - add this to Any.v ------------------". }
        rewrite Any_pair_downcast.
        steps.
        guclo bindC_spec.
        replace (Ordinal.from_nat 168) with (Ordinal.add (Ordinal.from_nat 68) (Ordinal.from_nat 100)); cycle 1.
        { admit "ez - ordinal nat add". }
        econs.
        + gbase. unfold body_to_tgt, body_to_mid. eapply CIH; try refl.
          rr. esplits; ss; et. rewrite URA.unit_idl. clear - WFTGT x. admit "ez".
        + ii. ss. des_ifs_safe. des; ss. clarify.
          steps. esplits; eauto. steps. unfold put. steps. destruct p0; ss. steps.
          unfold handle_rE. destruct r0; ss. destruct l0; ss.
          { steps. }
          steps.
          unfold guarantee.
          steps.
          unfold discard.
          steps.
          unfold guarantee. steps. r in SIM. des; ss. rewrite Any.upcast_downcast. esplits; ss; eauto.
          clear - x3 WFTGT0.
          admit "ez".
      - ii. ss. des_ifs. des. (* rr in SIM0. des; ss. unfold RelationPairs.RelCompFun in *. ss. *)
        (* r in SIM0. des_ifs. des; ss. *)
        steps. clear_tac. instantiate (1:=125).
        unfold checkWf, assume; steps.
        des_ifs; ss.
        { steps. }
        steps.
        unshelve esplits; eauto.
        { clear - ST1. admit "ez". }
        steps. esplits; eauto.
        unfold forge; steps. esplits; et.
        steps. unshelve esplits; eauto. steps.
        fold interp_hCallE_src. fold (interp_hCallE_tgt stb mn).
        gbase. eapply CIH; [refl|ss|..]; cycle 1.
        { refl. }
        { unfold interp_hCallE_tgt. erewrite Any.downcast_upcast; et. }
        rr. esplits; et. { destruct l2; ss. } clear - ST1. admit "ez".
    }
  Unshelve.
    all: ss.
    all: try (by apply Ordinal.O).
    { apply x6. }
  Qed.

  Hypothesis MAIN: List.find (fun '(_fn, _) => dec "main" _fn) stb = Some ("main",
    (* (@mk "Main" unit (fun _ varg_high _ _ => varg_high = tt↑) (fun _ vret_high _ _ => vret_high = tt↑) (fun _ => None))). *)
    (@mk_simple "Main" unit (fun _ _ _ o => o = ord_top) top3)).
  Hypothesis WFR: URA.wf (rsum (ModSem.initial_r_state ms_tgt)).

  Opaque interp_Es.
  Theorem adequacy_type_t2m: Beh.of_program (Mod.interp md_tgt) <1= Beh.of_program (Mod.interp md_mid).
  Proof.
    eapply adequacy_global.
    exists (Ordinal.from_nat 100%nat). ss.
    ginit.
    { eapply cpn5_wcompat; eauto with paco. }
    unfold ModSem.initial_itr. Local Opaque ModSem.prog. ss.
    unfold ITree.map.
    unfold assume.
    steps.
    esplits; et. { admit "ez - wf". }
    set (st_mid0 := ((ModSem.initial_r_state ms_mid), (ModSem.initial_p_state ms_mid))).
    replace (Mod.enclose md_tgt) with ms_tgt by ss.
    set (st_tgt0 := ((ModSem.initial_r_state ms_tgt), (ModSem.initial_p_state ms_tgt))).
    (* Local Opaque URA.add. *)
    assert(SIM: wf st_mid0 st_tgt0).
    { r. ss. esplits; ss; et. unfold ms_mid. unfold ModSem.initial_p_state. ss.
      apply func_ext. clear - Σ. i. rewrite ! find_map; ss. unfold compose. uo. unfold ms_tgt.
      des_ifs; ss; apply_all_once find_some; des; ss; des_sumbool; clarify.
      - destruct p0; ss. admit "ez - uniqueness of s".
      - eapply find_none in Heq0; et. ss. des_sumbool; ss.
      - eapply find_none in Heq1; et. des_ifs. ss. des_sumbool; ss.
    }
    unfold mrec.
    (* { *)
    (*   unfold ModSem.prog at 4. *)
    (*   unfold ModSem.prog at 2. *)
    (*   unfold unwrapU at 1. des_ifs; cycle 1. { steps. } steps. *)
    (*   rename Heq into MAINSRC. rename i into i_src. *)
    (*   assert(T: exists i_ftb i_tgt, *)
    (*             (<<MAINTGT:find (fun fnsem => dec "main" (fst fnsem)) (ModSem.fnsems ms_tgt) = *)
    (*                        Some ("main", i_tgt)>>) *)
    (*             /\ (<<FTB: In ("main", i_ftb) ftb>>) *)
    (*             /\ (<<SIM: i_tgt = fun_to_tgt stb "main" i_ftb>>) *)
    (*             /\ (<<SIM: i_src = fun_to_src i_ftb>>) *)
    (*         ). *)
    (*   { apply find_some in MAINSRC. des; ss. des_sumbool. clarify. *)
    (*     apply in_map_iff in MAINSRC. des. des_ifs. *)
    (*     destruct (find (fun fnsem => dec "main" (fst fnsem)) (ModSem.fnsems ms_tgt)) eqn:T; *)
    (*       rewrite WTY in *; ss; cycle 1. *)
    (*     - eapply find_none in T; ss; et. *)
    (*       { des_sumbool. instantiate (1:= (_, _)) in T. ss. } *)
    (*       rewrite in_map_iff. eexists (_, _). esplits; et. *)
    (*     - apply find_some in T. des; ss. des_sumbool. destruct p; ss. clarify. *)
    (*       rewrite in_map_iff in T. des; ss. des_ifs. *)
    (*       esplits; et. assert(i = i1) by admit "ez - add nodup". clarify. *)
    (*   } *)
    (*   des. clarify. *)
    (*   unfold unwrapU. des_ifs; cycle 1. steps. *)
    (*   unfold fun_to_tgt. des_ifs. ss. unfold fun_to_src. unfold HoareFun. *)
    (*   steps. esplits; et. steps. esplits; et. steps. *)
    (* } *)
    remember (x <- interp_Es (ModSem.prog ms_tgt) (ModSem.prog ms_tgt (Call "main" (Any.upcast []))) st_tgt0;; Ret (snd x)) as tmp.
    replace (([]: list val)↑) with (Any.pair ord_top↑ ([]: list val)↑) by admit "
      TODO: parameterize semantics with initial value of main; also, use this same initial value in Hoareproof1".
    subst.
    assert(TRANSL: simg eq (Ordinal.from_nat 100)
(x0 <- interp_Es (ModSem.prog ms_mid)
                 ((ModSem.prog ms_mid) _ (Call "main" (Any.pair ord_top↑ ([]: list val)↑))) st_mid0;; Ret (snd x0))
(x0 <- interp_Es (ModSem.prog ms_mid)
                 (interp_hCallE_mid (E:=pE +' eventE) ord_top (trigger (hCall false "main" ([]: list val)↑))) st_mid0;; Ret (snd x0))).
    { clear SIM. ginit. { eapply cpn5_wcompat; eauto with paco. }
      unfold interp_hCallE_mid. rewrite unfold_interp. ss. cbn. steps. unfold guarantee. steps.
      replace (Ordinal.from_nat 95) with (Ordinal.add (Ordinal.from_nat 50) (Ordinal.from_nat 45))
        by admit "ez".
      guclo bindC_spec.
      eapply bindR_intro.
      - eapply simg_gpaco_refl. typeclasses eauto.
      - ii. des_ifs. ss. steps.
    }
    assert(TRANSR: simg eq (Ordinal.from_nat 100)
(x0 <- interp_Es (ModSem.prog ms_tgt)
                 (interp_hCallE_tgt (E:=pE +' eventE) stb "Main" ord_top (trigger (hCall false "main" ([]: list val)↑))) st_tgt0;; Ret (snd x0))
(x0 <- interp_Es (ModSem.prog ms_tgt)
                 ((ModSem.prog ms_tgt) _ (Call "main" ([]: list val)↑)) st_tgt0;; Ret (snd x0))).
    { clear SIM. ginit. { eapply cpn5_wcompat; eauto with paco. }
      unfold interp_hCallE_tgt. rewrite unfold_interp. steps.
      unfold HoareCall.
      destruct (find (fun mnr => dec "Main" (fst mnr)) (ModSem.initial_mrs ms_tgt)) eqn:MAINR; cycle 1.
      { exfalso. clear - WF1 Heq MAINR. admit "ez - use WF1". }
      destruct p; ss.
      assert(s = "Main") by admit "ez". clarify.
      rewrite Any.upcast_downcast.
      steps. eexists ((fst (fst st_tgt0)) "Main", ε). steps.
      unfold put, guarantee. steps. unfold st_tgt0. steps.
      ss.
      unshelve esplits; eauto.
      { refl. }
      steps. esplits; et. steps. unfold discard, guarantee. steps. esplits; et. steps. unshelve esplits; et.
      { instantiate (1:=ε). rewrite URA.unit_id. ss. }
      steps. unfold guarantee. steps. esplits; et. steps. exists (([]: list val)↑).
      replace (update
                 (fun mn0 : string =>
                    match find (fun mnr => dec mn0 (fst mnr)) (ModSem.initial_mrs ms_tgt) with
                    | Some r => fst (snd r)
                    | None => ε
                    end) "Main" (fst p), [ε], ModSem.initial_p_state ms_tgt) with st_tgt0; cycle 1.
      { unfold st_tgt0.
        unfold ModSem.initial_r_state. f_equal. f_equal. apply func_ext. i. unfold update. des_ifs; ss; clarify. }
      steps. esplits; et. steps. esplits; et. steps. unshelve esplits; eauto. { esplits; ii; ss; et. rr. ss. } steps.
      replace (Ordinal.from_nat 47) with (Ordinal.add (Ordinal.from_nat 37) (Ordinal.from_nat 10)) by admit "ez".
      guclo bindC_spec.
      eapply bindR_intro with (RR:=eq).
      - fold st_tgt0. eapply simg_gpaco_refl. typeclasses eauto.
      - ii. des_ifs. ss. steps.
        unfold checkWf, assume. steps. destruct p0. steps.
        unfold ModSem.handle_rE. des_ifs.
        { admit "we should use stronger RR, not eq;
we should know that stackframe is not popped (unary property)". }
        steps. unfold forge; steps. des; ss.
    }



    fold ms_mid. fold st_mid0.
    replace (x0 <- interp_Es (ModSem.prog ms_mid) ((ModSem.prog ms_mid) _ (Call "main" (Any.pair ord_top↑ ([]: list val)↑))) st_mid0;;
             Ret (snd x0)) with
        (x0 <- interp_Es (ModSem.prog ms_mid) (interp_hCallE_mid (E:=pE +' eventE) ord_top (trigger (hCall false "main" ([]: list val)↑))) st_mid0;;
         Ret (snd x0)); cycle 1.
    { admit "hard -- by transitivity". }
    replace (x0 <- interp_Es (ModSem.prog ms_tgt) ((ModSem.prog ms_tgt) _ (Call "main" ([]: list val)↑)) st_tgt0;;
             Ret (snd x0)) with
        (x0 <- interp_Es (ModSem.prog ms_tgt) (interp_hCallE_tgt (E:=pE +' eventE) stb "Main" ord_top (trigger (hCall false "main" ([]: list val)↑)))
                         st_tgt0;; Ret (snd x0)); cycle 1.
    { admit "hard -- by transitivity". }
    guclo bindC_spec.
    eapply bindR_intro.
    - gfinal. right. fold simg. eapply adequacy_type_aux; ss. subst st_mid0 st_tgt0. ss.
    - ii. ss. des_ifs. des; ss. clarify. steps.
  Unshelve.
    all: ss.
    all: try (by apply Ordinal.O).
  Qed.

End CANCEL.
