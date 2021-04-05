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
From Ordinal Require Import Ordinal Arithmetic.

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

  Variable md_tgt: Mod.t.
  Let ms_tgt: ModSem.t := (Mod.get_modsem md_tgt (Sk.load_skenv md_tgt.(Mod.sk))).

  Variable sbtb: list (gname * fspecbody).
  Let stb: list (gname * fspec) := List.map (fun '(gn, fsb) => (gn, fsb_fspec fsb)) sbtb.
  Hypothesis WTY: ms_tgt.(ModSem.fnsems) = List.map (fun '(fn, sb) => (fn, fun_to_tgt stb fn sb)) sbtb.
  Let md_mid: Mod.t := md_mid md_tgt sbtb.
  Let ms_mid: ModSem.t := ms_mid md_tgt sbtb.

  Let W: Type := (r_state * p_state).
  Let rsum: r_state -> Σ :=
    fun '(mrs_tgt, frs_tgt) => (fold_left (⋅) (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε) ⋅ (fold_left (⋅) frs_tgt ε).
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
  Hypothesis WF1: Forall (fun '(_, sp) => In sp.(mn) (List.map fst ms_tgt.(ModSemL.initial_mrs))) stb.


  (* Ltac grind := repeat (f_equiv; try apply func_ext; ii; try (des_ifs; check_safe)). *)

  (* Ltac igo := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r; try rewrite bind_tau; *)
  (*                     try rewrite interp_vis; *)
  (*                     try rewrite interp_ret; *)
  (*                     try rewrite interp_tau *)
  (*                     (* try rewrite interp_trigger *) *)
  (*                    ). *)


  Let adequacy_type_aux:
    forall RT
           st_src0 st_tgt0 (SIM: wf st_src0 st_tgt0) (i0: itree (hCallE +' pE +' eventE) RT)
           mn cur
    ,
      (* sim (Mod.compile md_src) (Mod.compile md_tgt) lt 100%nat *)
      (*     (x <- (interp_Es p_src (interp_hCallE_src (trigger ce)) st_src0);; Ret (snd x)) *)
      (*     (x <- (interp_Es p_tgt (interp_hCallE_tgt stb (trigger ce)) st_tgt0);; Ret (snd x)) *)
      simg (fun '((rs_src, v_src)) '((rs_tgt, v_tgt)) => wf rs_src rs_tgt /\ (v_src: RT) = v_tgt)
           (Ord.from_nat 100%nat)
           (interp_Es mn (ModSem.prog ms_mid) (interp_hCallE_mid (E:=pE +' eventE) cur i0) st_src0)
           (interp_Es mn (ModSem.prog ms_tgt) (interp_hCallE_tgt (E:=pE +' eventE) stb cur i0) st_tgt0)
  .
  Proof.
    ginit.
    { i. eapply cpn5_wcompat; eauto with paco. }
    (* remember (` x : ModSemL.r_state * R <- interp_Es p_src (interp_hCallE_src (trigger ce)) st_src0;; Ret (snd x)) as tmp. *)
    gcofix CIH. i; subst.
    (* intros ? ?. *)
    (* pcofix CIH. i. *)
    unfold interp_hCallE_mid.
    unfold interp_hCallE_tgt.
    ides i0; try rewrite ! unfold_interp; cbn; mred.
    { steps. }
    { steps. gbase. eapply CIH; [..|M]; Mskip et. ss. }
    destruct e; cycle 1.
    {
      Opaque interp_Es.
      destruct s; ss.
      {
        destruct st_src0 as [rst_src0 pst_src0], st_tgt0 as [rst_tgt0 pst_tgt0]; ss. des_ifs. des; clarify.
        destruct p; ss.
        - steps. Esred. steps. gbase. eapply CIH. ss.
        - steps. Esred. steps. gbase. eapply CIH. ss.
      }
      { dependent destruction e.
        - steps. Esred. steps. esplits; eauto. steps.
          gbase. eapply CIH; [..|M]; Mskip et. ss.
        - steps. Esred. steps. esplits; eauto. steps.
          gbase. eapply CIH; [..|M]; Mskip et. ss.
        - steps. Esred. steps.
          gbase. eapply CIH; [..|M]; Mskip et. ss.
      }
    }
    dependent destruction h.
    set (ModSemL.prog ms_mid) as p_mid in *.
    set (ModSemL.prog ms_tgt) as p_tgt in *.
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
    (* unfold ModSemL.prog at 2. steps. *)
    unfold HoareCall.
    steps. unfold put, guarantee. steps.
    destruct st_tgt0 as [rst_tgt0 pst_tgt0]. destruct st_src0 as [rst_src0 pst_src0].
    Opaque interp_Es. (*** TODO: move to ModSemL ***)
    destruct (varg_src↓) eqn:CAST; cycle 1.
    { steps. }
    steps. unfold handle_rE. destruct rst_tgt0 as [mrs_tgt0 [|frs_tgt_hd frs_tgt_tl]] eqn:T; ss.
    { rr in SIM. des_ifs_safe. des; ss. destruct l; ss. }



    (*** exploiting both_tau ***)
    unseal_left. ired_all. steps.




    unfold discard. steps.
    unfold guarantee. steps. (*** TODO: remove: unfold guarantee ***)
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
    destruct tbr.
    { des; et. Opaque ord_lt. destruct x4; ss; cycle 1. { exfalso. exploit x7; et. } steps. esplits; eauto. steps. esplits; eauto. steps. unfold unwrapU.
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
      instantiate (1:=399).
      mred. steps.
      rename i into i_src.
      rename i0 into i_tgt.
      guclo bindC_spec.
      replace (Ord.from_nat 400) with
          (OrdArith.add (Ord.from_nat 200) (Ord.from_nat 200)); cycle 1.
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
        replace (Ord.from_nat 158) with (OrdArith.add (Ord.from_nat 58) (Ord.from_nat 100)); cycle 1.
        { admit "ez - ordinal nat add". }
        econs.
        + gbase. eapply CIH. rr. esplits; ss; et. rewrite URA.unit_idl. clear - WFTGT x. admit "ez".
        + ii. ss. des_ifs_safe. des; ss. clarify. des_u.
          steps. esplits; eauto. steps. unfold put. steps. destruct p0; ss. steps.
          unfold handle_rE. destruct r0; ss. destruct l; ss.
          { steps. }
          steps.
          unfold guarantee.
          steps.
          unfold discard.
          steps.
          unfold guarantee. steps. r in SIM. des; ss. rewrite Any.upcast_downcast. esplits; ss; eauto.
          clear - x3 WFTGT0.
          admit "ez".
      - ii. ss. des_ifs_safe. des. (* rr in SIM0. des; ss. unfold RelationPairs.RelCompFun in *. ss. *)
        (* r in SIM0. des_ifs. des; ss. *)
        unfold checkWf, assume; steps. clear_tac. esplits. steps.
        unfold forge; steps. des_ifs; ss. { steps. } steps. exists vret_src'. instantiate (1:=rret). esplits; et.
        steps. unshelve esplits; eauto. { clear - ST1. admit "ez". } steps. unshelve esplits; eauto. steps.
        fold (interp_hCallE_mid). fold (interp_hCallE_tgt stb).
        gbase. eapply Any.downcast_upcast in CAST0. des. subst. eapply CIH.
        rr. esplits; et. { destruct l2; ss. } clear - ST1. admit "ez".
    }
    { des. clear x7. exploit x8; et. i; clarify. clear x8.
      steps. esplits; eauto. steps. esplits; eauto. steps. unfold unwrapU.
      destruct (find (fun fnsem => dec fn (fst fnsem)) (List.map (fun '(fn0, sb) => (fn0, fun_to_mid (fsb_body sb))) sbtb)) eqn:FINDFS; cycle 1.
      { steps. }
      destruct (find (fun fnsem => dec fn (fst fnsem)) (ModSem.fnsems ms_tgt)) eqn:FINDFT0; cycle 1.
      { exfalso.
        rewrite WTY in *. ss. clear - FINDFS FINDFT0.
        rewrite find_map in *. uo. des_ifs.
        apply_all_once find_some. des.
        eapply find_none in Heq0; eauto.
        unfold compose in *. des_ifs. ss. des_sumbool. ss.
      }
      mred. des_ifs. mred.
      rename i into i_src.
      rename i0 into i_tgt.
      guclo bindC_spec.
      replace (Ord.from_nat 405) with
          (OrdArith.add (Ord.from_nat 205) (Ord.from_nat 200)); cycle 1.
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
        replace (Ord.from_nat 158) with (OrdArith.add (Ord.from_nat 58) (Ord.from_nat 100)); cycle 1.
        { admit "ez - ordinal nat add". }
        econs.
        + gbase. unfold body_to_tgt, body_to_mid. eapply CIH.
          rr. esplits; ss; et. rewrite URA.unit_idl. clear - WFTGT x. admit "ez".
        + ii. ss. des_ifs_safe. des; ss. clarify.
          steps. esplits; eauto. steps. unfold put. steps. destruct p0; ss. steps.
          unfold handle_rE. destruct r0; ss. destruct l; ss.
          { steps. }
          steps.
          unfold guarantee.
          steps.
          unfold discard.
          steps.
          unfold guarantee. steps. r in SIM. des; ss. rewrite Any.upcast_downcast. esplits; ss; eauto.
          clear - x3 WFTGT0.
          admit "ez".
      - ii. ss. des_ifs_safe. des. (* rr in SIM0. des; ss. unfold RelationPairs.RelCompFun in *. ss. *)
        (* r in SIM0. des_ifs. des; ss. *)
        steps. clear_tac. esplits. steps.
        unfold forge, checkWf, assume; steps.
        des_ifs; ss.
        { steps. }
        steps. esplits. steps. instantiate (1:= rret). instantiate (1:=vret_src').
        unshelve esplits; eauto.
        { clear - ST1. admit "ez". }
        steps. unshelve esplits; eauto.
        steps.
        fold interp_hCallE_src. fold (interp_hCallE_tgt stb).
        gbase. eapply Any.downcast_upcast in CAST0. des. subst. eapply CIH.
        rr. esplits; et. { destruct l2; ss. } clear - ST1. admit "ez".
    }
  Unshelve.
    all: ss.
    all: try (by apply Ord.O).
    { apply 0. }
  Qed.

  Variable entry_r: Σ.
  Variable main_pre: unit -> Any.t -> ord -> Σ -> Prop.
  Hypothesis MAINPRE: main_pre tt ([]: list val)↑ ord_top entry_r.
  Hypothesis MAIN: List.find (fun '(_fn, _) => dec "main" _fn) stb = Some ("main", (@mk_simple _ "Main" unit main_pre top3)).
  Hypothesis WFR: URA.wf (entry_r ⋅ rsum (ModSemL.initial_r_state ms_tgt)).

  Let initial_r_state ms entry_r: r_state :=
    (fun mn => match List.find (fun mnr => dec mn (fst mnr)) ms.(ModSemL.initial_mrs) with
               | Some r => fst (snd r)
               | None => ε
               end, [entry_r]). (*** we have a dummy-stack here ***)
  Lemma initial_r_state_spec: forall ms, initial_r_state ms ε = ModSemL.initial_r_state ms.
  Proof. refl. Qed.

  Opaque interp_Es.
  Opaque EventsL.interp_Es.

  Theorem adequacy_type_t2m: Beh.of_program (ModL.compile md_tgt) <1= Beh.of_program (ModL.compile md_mid).
  Proof.
    eapply adequacy_global.
    exists (Ord.from_nat 100%nat). ss.
    ginit.
    { eapply cpn5_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr. Local Opaque ModSemL.prog. ss.
    unfold ITree.map.
    unfold assume.
    steps.
    esplits; et. { admit "ez - wf". } steps.
    folder.
    set (st_mid0 := ((ModSemL.initial_r_state ms_mid), (ModSemL.initial_p_state ms_mid))).
    set (st_midmid0 := ((initial_r_state ms_tgt entry_r), (ModSemL.initial_p_state ms_tgt))).
    set (st_tgt0 := (ModSemL.initial_r_state ms_tgt, (ModSemL.initial_p_state ms_tgt))).
    (* Local Opaque URA.add. *)
    assert(SIM: wf st_mid0 st_midmid0).
    { r. ss. esplits; ss; et. { admit "ez". } unfold ms_mid. unfold ModSemL.initial_p_state. ss.
      apply func_ext. clear - Σ. i. des_ifs; des_sumbool; ss.
    }
    unfold mrec.
    (* { *)
    (*   unfold ModSemL.prog at 4. *)
    (*   unfold ModSemL.prog at 2. *)
    (*   unfold unwrapU at 1. des_ifs; cycle 1. { steps. } steps. *)
    (*   rename Heq into MAINSRC. rename i into i_src. *)
    (*   assert(T: exists i_ftb i_tgt, *)
    (*             (<<MAINTGT:find (fun fnsem => dec "main" (fst fnsem)) (ModSemL.fnsems ms_tgt) = *)
    (*                        Some ("main", i_tgt)>>) *)
    (*             /\ (<<FTB: In ("main", i_ftb) ftb>>) *)
    (*             /\ (<<SIM: i_tgt = fun_to_tgt stb "main" i_ftb>>) *)
    (*             /\ (<<SIM: i_src = fun_to_src i_ftb>>) *)
    (*         ). *)
    (*   { apply find_some in MAINSRC. des; ss. des_sumbool. clarify. *)
    (*     apply in_map_iff in MAINSRC. des. des_ifs. *)
    (*     destruct (find (fun fnsem => dec "main" (fst fnsem)) (ModSemL.fnsems ms_tgt)) eqn:T; *)
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
    match goal with | [ |- gpaco5 _ _ _ _ _ _ _ _ ?x ] => remember x as tmp end.
    replace (([]: list val)↑) with (Any.pair ord_top↑ ([]: list val)↑) by admit "
      TODO: parameterize semantics with initial value of main; also, use this same initial value in Hoareproof1".
    subst.
    assert(TRANSL: simg eq (Ord.from_nat 100)
(x0 <- EventsL.interp_Es (ModSemL.prog ms_mid)
                         ((ModSemL.prog ms_mid) _ (Call "main" (Any.pair ord_top↑ ([]: list val)↑))) st_mid0;; Ret (snd x0))
(x0 <- interp_Es "Main" (ModSem.prog ms_mid)
                 (interp_hCallE_mid (E:=pE +' eventE) ord_top (trigger (hCall false "main" ([]: list val)↑))) st_mid0;; Ret (snd x0))).
    { clear SIM. ginit. { eapply cpn5_wcompat; eauto with paco. }
      unfold interp_hCallE_mid. rewrite unfold_interp. ss. cbn. steps. unfold guarantee. Opaque ModSem.prog. steps.
      replace (Ord.from_nat 91) with (OrdArith.add (Ord.from_nat 50) (Ord.from_nat 41))
        by admit "ez".
      guclo bindC_spec.
      eapply bindR_intro.
      - instantiate (1:=eq).
        fold ms_tgt.
        replace
          (fun mn =>
             match (if sumbool_to_bool (dec mn (ModSem.mn ms_tgt)) then Some (ModSem.mn ms_tgt, (ε, ModSem.initial_st ms_tgt)) else None) with
             | Some r => fst (snd r)
             | None => ε
             end, [ε; ε]) with (ModSemL.initial_r_state ms_mid); cycle 1.
        { unfold ModSemL.initial_r_state. cbn. f_equal. admit "-----------------------------------------------------------------------------FIXME!!!!!!!!!". }
        replace (@pair (prod _ _) _ (ModSemL.initial_r_state ms_mid) (ModSemL.initial_p_state ms_mid)) with st_mid0 by refl.
        rewrite ModSem.lift_lemma.
        TTTTTTTTTTTTTTTT
        eapply find_some in Heq. des; ss. des_sumbool. subst. rewrite in_map_iff in *. des. des_ifs.
        (* assert(LEMMA: forall (md: ModSem.t) R (itr: itree _ R) st0, EventsL.interp_Es (ModSemL.prog md) (transl_all md.(ModSem.mn) itr) st0 = *)
        (*                                                             interp_Es md.(ModSem.mn) (ModSem.prog md) itr st0). *)
        (* { i. *)
        (*   Local Transparent interp_Es. unfold interp_Es. Local Opaque interp_Es. *)
        (*   des_ifs. *)
        (*   Local Transparent ModSemL.prog. unfold ModSemL.prog. Local Opaque ModSemL.prog. *)
        (*   refl. *)
        (*   unfold ModSemL.prog. *)
        (* } *)
        eapply simg_gpaco_refl. typeclasses eauto.
      - ii. des_ifs. ss. steps. interp_red. steps.
      
      folder.


        rewrite WF0 in MAIN.
        eapply find_none in Heq; cycle 1.
        { rewrite in_map_iff. eexists (_, _); ss. esplits; et.
        rewrite find_map in Heq. uo. rewrite WF0 in Heq. eapply find_none in Heq; cycle 1.
        { rewrite in_map_iff. eexists (_, _); ss. esplits; et.
      replace (Ord.from_nat 95) with (OrdArith.add (Ord.from_nat 50) (Ord.from_nat 45))
        by admit "ez".
      guclo bindC_spec.
      eapply bindR_intro.
      - eapply simg_gpaco_refl. typeclasses eauto.
      - ii. des_ifs. ss. steps. interp_red. steps.
    }
    assert(TRANSR: simg eq (Ord.from_nat 100)
(x0 <- interp_Es "Main" (ModSem.prog ms_tgt)
                 (interp_hCallE_tgt (E:=pE +' eventE) stb ord_top (trigger (hCall false "main" ([]: list val)↑))) st_midmid0;; Ret (snd x0))
(x0 <- EventsL.interp_Es (ModSemL.prog ms_tgt)
                 ((ModSemL.prog ms_tgt) _ (Call "main" ([]: list val)↑)) st_tgt0;; Ret (snd x0))).
(*     { clear SIM. ginit. { eapply cpn5_wcompat; eauto with paco. } *)
(*       unfold interp_hCallE_tgt. rewrite unfold_interp. steps. rewrite MAIN. steps. *)
(*       unfold HoareCall. *)
(*       destruct (find (fun mnr => dec "Main" (fst mnr)) (ModSemL.initial_mrs ms_tgt)) eqn:MAINR; cycle 1. *)
(*       { exfalso. clear - WF1 MAIN MAINR. admit "ez - use WF1". } *)
(*       destruct p; ss. *)
(*       assert(s = "Main") by admit "ez". clarify. *)
(*       rewrite Any.upcast_downcast. *)
(*       steps. eexists ((fst (fst st_tgt0)) "Main", entry_r). steps. *)
(*       unfold put, guarantee. steps. unshelve esplits; eauto. { refl. } *)
(*       steps. esplits; et. steps. unfold discard, guarantee. steps. esplits; et. steps. unshelve esplits; et. *)
(*       { rewrite URA.unit_id. ss. } *)
(*       steps. unfold guarantee. steps. esplits; ss; et. steps. exists (([]: list val)↑). *)
(*       replace (update *)
(*                  (fun mn0 : string => *)
(*                     match find (fun mnr => dec mn0 (fst mnr)) (ModSemL.initial_mrs ms_tgt) with *)
(*                     | Some r => fst (snd r) *)
(*                     | None => ε *)
(*                     end) "Main" (fst p), [ε], ModSemL.initial_p_state ms_tgt) with st_tgt0; cycle 1. *)
(*       { unfold st_tgt0. *)
(*         unfold ModSemL.initial_r_state. f_equal. f_equal. apply func_ext. i. unfold update. des_ifs; ss; clarify. } *)
(*       steps. esplits; et. steps. esplits; et. steps. unshelve esplits; eauto. { ss. } steps. *)
(*       replace (Ord.from_nat 47) with (OrdArith.add (Ord.from_nat 37) (Ord.from_nat 10)) by admit "ez". *)
(*       guclo bindC_spec. *)
(*       eapply bindR_intro with (RR:=eq). *)
(*       - fold st_tgt0. eapply simg_gpaco_refl. typeclasses eauto. *)
(*       - ii. des_ifs. ss. steps. *)
(*         unfold forge, checkWf, assume. steps. destruct p0. steps. *)
(*         unfold ModSemL.handle_rE. des_ifs. *)
(*         { admit "we should use stronger RR, not eq; *)
(* we should know that stackframe is not popped (unary property)". } *)
(*         steps. interp_red. des; ss. steps. *)
(*     } *)
    { admit "". }



    fold ms_mid. fold st_mid0.
    replace (x <- EventsL.interp_Es (ModSemL.prog ms_mid) (ModSemL.prog ms_mid (Call "main" (Any.pair (Any.upcast ord_top) (Any.upcast [])))) st_mid0;; Ret (snd x))
      with
        (x0 <- interp_Es "Main" (ModSem.prog ms_mid) (interp_hCallE_mid (E:=pE +' eventE) ord_top (trigger (hCall false "main" ([]: list val)↑))) st_mid0;;
         Ret (snd x0)); cycle 1.
    { admit "hard -- by transitivity". }
    replace (x <- EventsL.interp_Es (ModSemL.prog ms_tgt) (ModSemL.prog ms_tgt (Call "main" (Any.upcast []))) st_tgt0;; Ret (snd x))
      with
        (x0 <- interp_Es "Main" (ModSem.prog ms_tgt) (interp_hCallE_tgt (E:=pE +' eventE) stb ord_top (trigger (hCall false "main" ([]: list val)↑)))
                         st_midmid0;; Ret (snd x0)); cycle 1.
    { admit "hard -- by transitivity". }
    guclo bindC_spec.
    eapply bindR_intro.
    - gfinal. right. fold simg. eapply adequacy_type_aux; ss.
    - ii. ss. des_ifs. des; ss. clarify. steps.
  Unshelve.
    revert WFR. i. (*** dummy action that keeps "WFR" as a requirement; TODO: remove it later ! ! ***)
    all: ss.
    all: try (by apply Ord.O).
  Qed.

End CANCEL.
