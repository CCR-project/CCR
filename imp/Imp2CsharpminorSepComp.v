From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory Csharpminor Linking.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.
Require Import Imp2Csharpminor.
Require Import ImpProofs.
Require Import SimSTS2.
Require Import Mem0.
Require Import IRed.
From Ordinal Require Import Ordinal Arithmetic.

Require Import Imp2CsharpminorMatch.
Require Import Imp2CsharpminorArith.
Require Import Imp2CsharpminorGenv.
Require Import Imp2CsharpminorMem.
Require Import Imp2CsharpminorLink.
Require Import Imp2CsharpminorSim.

Set Implicit Arguments.

Section PROOFALL.

  Import Maps.PTree.

  Context `{Σ: GRA.t}.

  Create HintDb ord_step2.
  Hint Resolve Nat.lt_succ_diag_r OrdArith.lt_from_nat OrdArith.lt_add_r: ord_step2.
  Hint Extern 1000 => lia: ord_step2.
  Ltac ord_step2 := eauto with ord_step2.

  (* Import ModSemL. *)

  (* Let _sim_mon := Eval simpl in (fun (src: ModL.t) (tgt: Csharpminor.program) => @sim_mon (ModL.compile src) (semantics tgt)). *)
  (* Hint Resolve _sim_mon: paco. *)

  (* Let _ordC_spec := *)
  (*   Eval simpl in (fun (src: ModL.t) (tgt: Csharpminor.program) => @ordC_spec (ModL.compile src) (Csharpminor.semantics tgt)). *)

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); econs 3; ss; clarify; eexists; exists (ModSemL.step_tau _); eexists; split; [ord_step2|auto].
  (* Ltac sim_ord := guclo _ordC_spec; econs. *)

  Ltac sim_triggerUB := unfold triggerUB; (try sim_red); econs 5; i; ss; auto;
                        dependent destruction STEP; try (irw in x; clarify; fail).

  Definition imp_initial_state (src : Imp.programL) :=
    (ModL.compile (ModL.add (Mod.lift Mem) (ImpMod.get_modL src))).(initial_state).

  Lemma single_compile_behavior_improves
        (src: Imp.programL) (tgt: Csharpminor.program) srcst tgtst
        (WFPROG: Permutation.Permutation
                   ((List.map fst src.(prog_varsL)) ++ (List.map (compose fst snd) src.(prog_funsL)))
                   (List.map fst src.(defsL)))
        (WFPROG2 : forall gn gv, In (gn, Sk.Gvar gv) (Sk.sort (defsL src)) -> In (gn, gv) (prog_varsL src))
        (COMP: Imp2Csharpminor.compile src = OK tgt)
        (SINIT: srcst = imp_initial_state src)
        (TINIT: Csharpminor.initial_state tgt tgtst)
    :
      <<IMPROVES: @improves2 _ (Csharpminor.semantics tgt) srcst tgtst>>.
  Proof.
    eapply adequacy; eauto.
    { apply Ordinal.Ord.lt_well_founded. }
    { apply Csharpminor_wf_semantics. }
    { admit "ez? wf imp". }
    instantiate (1:= ((100 + max_fuel) + 120)%ord). red. unfold imp_initial_state in *. ss; clarify. inv TINIT.
    rename m0 into tm, ge into tge, H into TMINIT, H0 into TMAIN1, H1 into TMAIN2, H2 into TSIGMAIN, b into tb, f into tmain.
    assert (COMP0: Imp2Csharpminor.compile src = OK tgt); auto. move COMP0 before tgt.
    unfold compile in COMP. des_ifs. rename g into gm, Heq into GMAP.
    unfold _compile in COMP. des_ifs. rename Heq into COMPGDEFS, l0 into NOREPET. ss; clarify.
    match goal with | [ COMP0 : compile _ = OK ?_tgt |- _ ] => set (tgt:=_tgt) in * end.
    unfold ModSemL.initial_itr. unfold ModSemL.initial_itr_arg.
    pfold. econs 5; eauto. unfold assume. ss. grind. eapply angelic_step in STEP. des; clarify. eexists; split; [ord_step2|auto].
    left. unfold ITree.map. sim_red. set (sge:=Sk.load_skenv (Sk.sort (defsL src))) in *.
    destruct (alist_find "main" (List.map (fun '(mn, (fn, f)) => (fn, transl_all mn ∘ cfun (eval_imp sge f))) (prog_funsL src)))
             eqn:FOUNDMAIN; ss; grind.
    2:{ pfold. sim_triggerUB. }
    rewrite alist_find_find_some in FOUNDMAIN. rewrite find_map in FOUNDMAIN. uo; des_ifs; ss.
    rename s into mn, f into smain, Heq into SFOUND. apply find_some in SFOUND. des. ss. clear SFOUND0.
    assert (COMPGDEFS0 : compile_gdefs gm src = Some l); auto.
    unfold compile_gdefs in COMPGDEFS. uo; des_ifs. ss. rename l0 into cfs.
    match goal with | [ H: Coqlib.list_norepet (List.map fst ?_l) |- _ ] => set (tgds:=_l) in * end.
    hexploit exists_compiled_function; eauto. i; des. rename H into PCMAIN, H0 into INPMAIN, H1 into CFMAIN, H2 into INFMAIN.
    hexploit in_tgt_prog_defs_ifuns; eauto. i. rename H into INFMAINTGT.
    hexploit tgt_genv_find_def_by_blk; eauto. i. rename H into TGTMAIN. ss; clarify. uo; des_ifs; ss; clarify.
    2:{ rewrite eq_rel_dec_correct in Heq; des_ifs. }
    match goal with [H: Genv.find_def _ _ = Some (Gfun (Internal ?tf)) |- _ ] => set (tmainf:=tf) in * end.
    unfold Genv.find_funct_ptr in TMAIN2. des_ifs. rename Heq2 into TMAIN2.
    hexploit tgt_genv_match_symb_def.
    1,2,4: eauto.
    1: eapply TMAIN2.
    i; clarify. clear Heq. unfold pre_compile_function in PCMAIN. des_ifs; ss. clear INPMAIN.
    rename Heq1 into CMAINstmt, l into WF_MAIN, s into mstmt.
    unfold cfun. rewrite Any.upcast_downcast. grind. rewrite unfold_eval_imp_only. des_ifs; grind; sim_red.
    2:{ pfold. sim_triggerUB. }
    assert (MAINPARAM: fn_params smain = []).
    { depgen Heq. clear. i. remember (fn_params smain) as m. clear Heqm. depgen l. induction m; i; ss; clarify. }
    clear Heq. rewrite interp_imp_tau. sim_red.

    pfold. econs 4; ss. eexists. eexists.
    { apply Coqlib.list_norepet_app in WF_MAIN; des. subst tmainf.
      eapply step_internal_function; ss; eauto; try econs;
        match goal with [H: Genv.find_def _ _ = Some (Gfun (Internal ?tf)) |- _ ] => set (tmainf:=tf) in * end.
      rewrite MAINPARAM. ss. }
    eexists; split; [ord_step2|auto]. left. ss.

    pfold. econs 6; ss; eauto. eexists. eexists.
    { eapply step_seq. }
    eexists. exists (ModSemL.step_tau _). exists ((100 + max_fuel) + 100)%ord. left.
    rewrite interp_imp_bind. grind. sim_red. rename l into sle.
    assert (MATCHGE: match_ge src (Sk.sort (ModL.sk (ModL.add Mem (ImpMod.get_modL src)))) (Genv.globalenv tgt)).
    { econs. i. unfold map_blk. rewrite COMP0. hexploit Sk.env_found_range; eauto. i. unfold src_init_nb, int_len.
      rewrite <- sksort_same_len in H0. ss. des_ifs; unfold NW in *; try lia.
      - unfold get_sge in *. ss. apply Sk.sort_wf in SK.
        hexploit Sk.load_skenv_wf; eauto. i. apply H1 in H. rewrite H in Heq. clarify.
      - unfold get_sge in *. ss. apply Sk.sort_wf in SK.
        hexploit Sk.load_skenv_wf; eauto. i. apply H1 in H. rewrite H in Heq. clarify.
        hexploit found_in_src_in_tgt; eauto. i. des. rewrite Heq1 in H2. clarify.
      - unfold get_sge in *. ss. apply Sk.sort_wf in SK.
        hexploit Sk.load_skenv_wf; eauto. i. apply H1 in H. rewrite H in Heq. clarify. }
    eapply match_states_sim; eauto.
    { apply map_blk_after_init. }
    { apply map_blk_inj. }
    match goal with
    | [ |- match_states _ ?_ge ?_ms _ _ _ ] => replace _ge with sge; auto; set (ms:=_ms) in *
    end.
    econs; eauto.
    { admit "ez?: match initial le". }
    { clarify. }
    { econs; ss.
      { unfold src_init_nb, int_len. rewrite <- sksort_same_len. lia. }
      { apply Genv.init_mem_genv_next in TMINIT. rewrite <- TMINIT. unfold Genv.globalenv. ss.
        rewrite Genv.genv_next_add_globals. ss. rewrite Genv_advance_next_length. ss.
        rewrite length_elements_PTree_norepet; eauto. rewrite map_blk_after_init; eauto.
        2:{ unfold src_init_nb, int_len. rewrite <- sksort_same_len. lia. }
        unfold ext_len. subst tgds. repeat rewrite app_length. ss.
        rewrite <- sksort_same_len. rewrite wfprog_defsL_length; eauto.
        rewrite app_length. repeat rewrite map_length. apply get_iFuns_length in Heq0. rewrite <- Heq0.
        apply gmap_preserves_length in GMAP. des. rewrite EVL; rewrite EFL; rewrite IVL; rewrite IFL. lia. }
      i. uo; des_ifs. unfold NW in H. clarify. rename s into gn, Heq1 into SGENV.
      set (tblk:=map_blk src blk) in *. unfold map_ofs in *. rewrite! Z.mul_0_r.
      hexploit found_gvar_in_src_then_tgt; eauto. i. des. rename H into FOUNDTGV.
      hexploit Genv.init_mem_characterization; eauto.
      { unfold Genv.find_var_info. rewrite FOUNDTGV. clarify. }
      i. des. rename H into TMPERM, H0 into TMPERM0, H1 into TMLSID, H2 into TMLB.
      subst tblk. inv MATCHGE.
      assert (SKFOUND: SkEnv.blk2id sge blk = Some gn).
      { subst sge. Local Transparent Sk.load_skenv. unfold Sk.load_skenv. ss. rewrite SGENV. uo; ss. Local Opaque Sk.load_skenv. }
      assert (WFSKENV: Sk.wf (defsL src)); auto.
      apply Sk.sort_wf in WFSKENV. apply Sk.load_skenv_wf in WFSKENV. apply WFSKENV in SKFOUND. clear WFSKENV.
      apply MG in SKFOUND.
      (* apply WFPROG2 in SGENV. *)
      (* apply nth_error_In in SGENV. *)

(* Mem.load_store_same: *)
(*   forall (chunk : memory_chunk) (m1 : mem) (b : Values.block) (ofs : Z) (v : Values.val) (m2 : mem), *)
(*   Memory.Mem.store chunk m1 b ofs v = Some m2 -> Memory.Mem.load chunk m2 b ofs = Some (Values.Val.load_result chunk v) *)

      admit "mid: match init mem". }
    { ss. }
    { ss.
      match goal with
      | [ |- match_code _ _ _ _ ?i0 ?s0 ] =>
        replace i0 with ((fun '(r, p, (le, _)) => itree_of_imp_ret sge le ms mn (r, p)) : (_ * _ * (lenv * val)) -> _);
          replace s0 with [exit_stmt]; eauto
      end.
      { econs 1. }
      extensionality x. unfold itree_of_imp_ret, itree_of_imp_cont. grind. destruct p0. rewrite interp_imp_expr_Var. grind. }
    { ss.
      match goal with
      | [ |- match_stack _ _ _ _ _ ?i0 ?s0 ] =>
        replace i0 with ((itree_of_imp_pop_bottom ms mn) : (_ * _ * (lenv * val)) -> _);
          replace s0 with (Some ret_call_main); eauto
      end.
      { econs 1. } }
  Qed.


  (* Lemma list_norepet_NoDupB {K} {decK} : *)
  (*   forall l, Coqlib.list_norepet l <-> @NoDupB K decK l = true. *)
  (* Proof. *)
  (*   split; i. *)
  (*   - induction H; ss. *)
  (*     clarify. *)
  (*     destruct (in_dec decK hd tl); clarify. *)
  (*   - induction l; ss; clarify. constructor. *)
  (*     des_ifs. econs 2; auto. *)
  (* Qed. *)

  (* Definition wf_imp_prog (src : Imp.programL) := *)
  (*   Coqlib.list_norepet (compile_gdefs (get_gmap src) src). *)

  (* Lemma compile_then_wf : forall src tgt, *)
  (*     compile src = OK tgt *)
  (*     -> *)
  (*     wf_imp_prog src. *)
  (* Proof. *)
  (*   unfold compile, _compile. i. *)
  (*   destruct (compile_gdefs (get_gmap src) src) eqn:EQ; clarify. *)
  (*   eauto using compile_gdefs_then_wf. *)
  (* Qed. *)

  (* Maps.PTree.elements_extensional 
     we will rely on above theorem for commutation lemmas *)
  Lemma _comm_link_imp_compile
        src1 src2 srcl tgt1 tgt2 tgtl
        (COMP1: compile src1 = OK tgt1)
        (COMP2: compile src2 = OK tgt2)
        (LINKSRC: link_imp src1 src2 = Some srcl)
        (LINKTGT: link_prog tgt1 tgt2 = Some tgtl)
    :
      <<COMPL: compile srcl = OK tgtl>>.
  Proof.
  Admitted.

  Definition wf_link {T} (program_list : list T) :=
    exists h t, program_list = h :: t.

  Inductive compile_list :
    list programL -> list (Csharpminor.program) -> Prop :=
  | compile_nil :
      compile_list [] []
  | compile_head
      src_h src_t tgt_h tgt_t
      (COMPH: compile src_h = OK tgt_h)
      (COMPT: compile_list src_t tgt_t)
    :
      <<COMPLIST: compile_list (src_h :: src_t) (tgt_h :: tgt_t)>>.

  Definition fold_left_option {T} f (t : list T) (opth : option T) :=
    fold_left
      (fun opt s2 => match opt with | Some s1 => f s1 s2 | None => None end)
      t opth.

  Lemma fold_left_option_None {T} :
    forall f (l : list T), fold_left_option f l None = None.
  Proof.
    intros f. induction l; ss; clarify.
  Qed.

  Definition link_imp_list src_list :=
    match src_list with
    | [] => None
    | src_h :: src_t =>
      fold_left_option link_imp src_t (Some src_h)
    end.

  Definition link_csm_list (tgt_list : list (Csharpminor.program)) :=
    match tgt_list with
    | [] => None
    | tgt_h :: tgt_t =>
      fold_left_option link_prog tgt_t (Some tgt_h)
    end.

  Lemma comm_link_imp_compile
        src_list srcl tgt_list tgtl
        (COMPL: compile_list src_list tgt_list)
        (LINKSRC: link_imp_list src_list = Some srcl)
        (LINKTGT: link_csm_list tgt_list = Some tgtl)
    :
      compile srcl = OK tgtl.
  Proof.
    i. destruct src_list; destruct tgt_list; ss; clarify.
    inv COMPL; clarify.
    generalize dependent srcl. generalize dependent tgtl.
    generalize dependent p. generalize dependent p0.
    induction COMPT; i; ss; clarify.
    destruct (link_prog p0 tgt_h) eqn:LPt; ss; clarify.
    2:{ rewrite fold_left_option_None in LINKTGT; clarify. }
    destruct (link_imp p src_h) eqn:LPs; ss; clarify.
    2:{ rewrite fold_left_option_None in LINKSRC; clarify. }
    eapply IHCOMPT.
    2: apply LINKTGT.
    2: apply LINKSRC.
    eapply _comm_link_imp_compile.
    3: apply LPs.
    3: apply LPt.
    auto. auto.
  Qed.

  Lemma _comm_link_imp_link_mod
        src1 src2 srcl tgt1 tgt2 tgtl (ctx : ModL.t)
        (MOD1: ImpMod.get_modL src1 = tgt1)
        (MOD2: ImpMod.get_modL src2 = tgt2)
        (LINKIMP: link_imp src1 src2 = Some srcl)
        (MODL: ImpMod.get_modL srcl = tgtl)
    :
      <<LINKMOD: ModL.add (ModL.add ctx tgt1) tgt2 = ModL.add ctx tgtl>>.
  Proof.
  Admitted.

  Lemma comm_link_imp_link_mod
        src_list srcl tgt_list tgtl ctx
        (MODLIST: List.map (fun src => ImpMod.get_modL src) src_list = tgt_list)
        (LINKIMP: link_imp_list src_list = Some srcl)
        (MODL: ImpMod.get_modL srcl = tgtl)
    :
      <<LINKMOD: fold_left ModL.add tgt_list ctx = ModL.add ctx tgtl>>.
  Proof.
    destruct src_list eqn:SL; i; ss; clarify.
    move p after l.
    revert_until Σ.
    induction l; i; ss; clarify.
    destruct (link_imp p a) eqn:LI; ss; clarify.
    2:{ rewrite fold_left_option_None in LINKIMP; clarify. }
    erewrite _comm_link_imp_link_mod; eauto.
  Qed.

  Definition src_initial_state (src : ModL.t) :=
    (ModL.compile src).(initial_state).

  Theorem compile_behavior_improves
          (src_list : list Imp.program) srcl tgt_list tgtl srcst tgtst
          (COMP: let src_list_lift := List.map Imp.lift src_list in
                 compile_list src_list_lift tgt_list)
          (LINKSRC: let src_list_mod := List.map ImpMod.get_mod src_list in
                    Mod.add_list (Mem :: src_list_mod) = srcl)
          (LINKTGT: link_csm_list tgt_list = Some tgtl)
          (SINIT: srcst = src_initial_state srcl)
          (TINIT: Csharpminor.initial_state tgtl tgtst)
    :
      <<IMPROVES: @improves2 _ (Csharpminor.semantics tgtl) srcst tgtst>>.
  Proof.
  Admitted.

End PROOFALL.
