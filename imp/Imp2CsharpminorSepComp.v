From compcert Require Import Maps Globalenvs Smallstep AST Integers Events Behaviors Errors Memory Csharpminor Linking.
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

Section PROOFSINGLE.

  Context `{Σ: GRA.t}.

  Create HintDb ord_step2.
  Hint Resolve Nat.lt_succ_diag_r OrdArith.lt_from_nat OrdArith.lt_add_r: ord_step2.
  Hint Extern 1000 => lia: ord_step2.
  Ltac ord_step2 := eauto with ord_step2.

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); econs 3; ss; clarify; eexists; exists (ModSemL.step_tau _); eexists; split; [ord_step2|auto].

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
    unfold compile in COMP. des_ifs.
    match goal with | [ COMP0: compile _ = OK ?_tgt |- _ ] => set (tgt:=_tgt) in * end.
    rename l into NOREPET.
    unfold ModSemL.initial_itr. unfold ModSemL.initial_itr_arg.
    pfold. econs 5; eauto. unfold assume. ss. grind. eapply angelic_step in STEP. des; clarify.
    eexists; split; [ord_step2|auto].

    left. unfold ITree.map. sim_red.
    set (sge:=Sk.load_skenv (Sk.sort (defsL src))) in *.
    destruct (alist_find "main" (List.map (fun '(mn, (fn, f)) => (fn, transl_all mn ∘ cfun (eval_imp sge f))) (prog_funsL src)))
             eqn:FOUNDMAIN; ss; grind.
    2:{ pfold. sim_triggerUB. }
    rewrite alist_find_find_some in FOUNDMAIN. rewrite find_map in FOUNDMAIN. uo; des_ifs; ss.
    rename s into mn, f into smain, Heq into SFOUND. apply find_some in SFOUND. des. ss. clear SFOUND0.

    set (tgds:=compile_gdefs src) in *.
    hexploit in_compile_gdefs_ifuns; eauto. i. rename H into INFMAIN.
    hexploit in_tgt_prog_defs_ifuns; eauto. i. rename H into INFMAINTGT.
    hexploit tgt_genv_find_def_by_blk; eauto. i. rename H into TGTMAIN. ss; clarify.
    match goal with [H: Genv.find_def _ _ = Some (Gfun (Internal ?tf)) |- _ ] => set (tmainf:=tf) in * end.
    unfold cfun. rewrite Any.upcast_downcast. grind. rewrite unfold_eval_imp_only.
    sim_red. unfold assume. sim_red.
    pfold. econs 5; ss; eauto. i. eapply angelic_step in STEP; des; clarify.
    eexists; split; [ord_step2|auto]. left. rename STEP0 into WF_MAIN.
    do 4 (pfold; sim_tau; left). sim_red.

    des_ifs; grind; sim_red.
    2:{ pfold. sim_triggerUB. }
    assert (MAINPARAM: fn_params smain = []).
    { depgen Heq. clear. i. remember (fn_params smain) as m. clear Heqm. depgen l. induction m; i; ss; clarify. }
    rename l into sle, Heq into INITARGS. rewrite MAINPARAM in INITARGS. ss. clarify.
    rewrite interp_imp_tau. sim_red.

    unfold Genv.find_funct_ptr in TMAIN2. subst tge. rewrite TGTMAIN in TMAIN2. clarify.
    set (tge:=Genv.globalenv tgt) in *.
    pfold. econs 4; ss. eexists. eexists.
    { rewrite <- NoDup_norepeat in WF_MAIN. apply Coqlib.list_norepet_app in WF_MAIN; des. subst tmainf.
      rewrite MAINPARAM in *. eapply step_internal_function; ss; eauto; try econs. }
    eexists; split; [ord_step2|auto]. left. ss.

    pfold. econs 6; ss; eauto. eexists. eexists.
    { eapply step_seq. }
    eexists. exists (ModSemL.step_tau _). exists ((100 + max_fuel) + 100)%ord. left.
    rewrite interp_imp_bind. grind. sim_red.
    assert (MATCHGE: match_ge src (Sk.sort (ModL.sk (ModL.add Mem (ImpMod.get_modL src)))) (Genv.globalenv tgt)).
    { econs. i. unfold map_blk. rewrite COMP0. hexploit Sk.env_found_range; eauto. i. unfold src_init_nb, int_len.
      rewrite <- sksort_same_len in H0. ss. des_ifs; unfold NW in *; try lia.
      - unfold get_sge in *. ss. apply Sk.sort_wf in SK.
        hexploit Sk.load_skenv_wf; eauto. i. apply H1 in H. rewrite H in Heq. clarify.
      - unfold get_sge in *. ss. apply Sk.sort_wf in SK.
        hexploit Sk.load_skenv_wf; eauto. i. apply H1 in H. rewrite H in Heq. clarify.
        hexploit found_in_src_in_tgt; eauto. i. des. rewrite Heq0 in H2. clarify.
      - unfold get_sge in *. ss. apply Sk.sort_wf in SK.
        hexploit Sk.load_skenv_wf; eauto. i. apply H1 in H. rewrite H in Heq. clarify. }

    eapply match_states_sim; eauto.
    { apply map_blk_after_init. }
    { apply map_blk_inj. }
    ss.
    match goal with
    | [ |- match_states ?_ge ?_ms _ _ _ ] => replace _ge with sge; auto
    end.
    match goal with
    | [ |- match_states ?_ge ?_ms _ _ _ ] => set (ms:=_ms) in *
    end.
    econs; eauto.
    { ss. }
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
        rewrite gdefs_preserves_length. lia. }
      i. uo; des_ifs. unfold NW in H. clarify. rename s into gn, Heq0 into SGENV.
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
      apply MG in SKFOUND. apply nth_error_In in SGENV. apply WFPROG2 in SGENV.
      hexploit compiled_gvar_props; eauto. i. des. clarify.
      assert (TMLSID0: false = false); auto. apply TMLSID in TMLSID0; clear TMLSID.
      assert (TMLB0: false = false); auto. apply TMLB in TMLB0; clear TMLB.
      rewrite H0 in *. ss. des. clear TMLSID1. split; auto.
      unfold Genv.perm_globvar in TMPERM. des_ifs. split.
      2:{ unfold NW. lia. }
      split; eauto. ss. apply Z.divide_0_r. }
    { ss. }
    { ss.
      match goal with
      | [ |- match_code _ _ _ ?i0 ?s0 ] =>
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
      { econs 1. ss. }
      extensionality x. unfold itree_of_imp_pop_bottom. grind. sim_red. Red.prw ltac:(_red_gen) 1 0. ss.
    }
  Qed.

End PROOFSINGLE.





Section PROOFLEFT.

  Context `{Σ: GRA.t}.

  (* Proving the left arrow of the diagram *)
  Lemma _comm_link_imp_link_mod
        src1 src2 srcl tgt1 tgt2 tgtl (ctx : ModL.t)
        (MOD1: ImpMod.get_modL src1 = tgt1)
        (MOD2: ImpMod.get_modL src2 = tgt2)
        (LINKIMP: link_imp src1 src2 = Some srcl)
        (MODL: ImpMod.get_modL srcl = tgtl)
    :
      <<LINKMOD: ModL.add ctx (ModL.add tgt1 tgt2) = ModL.add ctx tgtl>>.
  Proof.
    unfold link_imp in LINKIMP. des_ifs; ss. unfold ImpMod.get_modL; ss. unfold ModL.add. ss. red. f_equal.
    extensionality sk. unfold ModSemL.add; ss. f_equal.
    - f_equal. rewrite <- map_app. ss.
    - f_equal. rewrite <- map_app. ss.
  Qed.

  Lemma comm_link_imp_link_mod
        src_list srcl tgt_list tgtl ctx
        (MODLIST: List.map ImpMod.get_modL src_list = tgt_list)
        (LINKIMP: link_imp_list src_list = Some srcl)
        (MODL: ImpMod.get_modL srcl = tgtl)
    :
      <<LINKMOD: fold_right ModL.add ModL.empty (ctx :: tgt_list) = ModL.add ctx tgtl>>.
  Proof.
    destruct src_list as [ | src0 src_liat ]; ss; clarify. des_ifs; ss; clarify.
    { rewrite ModL.add_empty_r. ss. }
    rename p into src1, p0 into srct, l into src_list, Heq into LINK. move src_list before Σ.
    revert_until Σ. induction src_list; i; ss; clarify.
    { rewrite ModL.add_empty_r. eapply _comm_link_imp_link_mod; eauto. }
    red. des_ifs; ss; clarify.
    { rewrite ModL.add_empty_r. eapply _comm_link_imp_link_mod; eauto.
      specialize IHsrc_list with (ctx:=ModL.empty). rewrite <- ModL.add_empty_l. sym; rewrite <- ModL.add_empty_l.
      replace (ImpMod.get_modL p) with (ModL.add (ImpMod.get_modL p) ModL.empty).
      2:{ apply ModL.add_empty_r. }
      eapply IHsrc_list; eauto. }
    hexploit _comm_link_imp_link_mod.
    5:{ i. eapply H. }
    4:{ clarify. }
    3:{ eapply LINKIMP. }
    all: eauto.
    specialize IHsrc_list with (ctx:=ModL.empty). rewrite <- ModL.add_empty_l. sym; rewrite <- ModL.add_empty_l.
    eapply IHsrc_list; eauto.
  Qed.

  Theorem left_arrow
          (src_list: list Imp.program) srcl (tgt_list: list Mod.t) tgtl (ctx: Mod.t)
          (MODLIST: List.map ImpMod.get_mod src_list = tgt_list)
          (LINKIMP: link_imps src_list = Some srcl)
          (MODL: ImpMod.get_modL srcl = tgtl)
    :
      <<LINKMOD: Mod.add_list (ctx :: tgt_list) = ModL.add (Mod.lift ctx) tgtl>>.
  Proof.
    red. unfold Mod.add_list. ss. eapply comm_link_imp_link_mod; eauto. rewrite List.map_map.
    pose ImpMod.comm_imp_mod_lift. unfold compose in e. rewrite e; clear e. rewrite <- List.map_map.
    rewrite MODLIST. ss.
  Qed.

End PROOFLEFT.





Section PROOFRIGHT.

  Import Permutation.

  Context `{Σ: GRA.t}.

  (* Proving the right arrow of the diagram *)

  (* Maps.PTree.elements_extensional 
     we will rely on above theorem for commutation lemmas *)
  Variable Q: list (ident * globdef fundef ()) -> list (ident * globdef fundef ()) -> list (ident * globdef fundef ()) -> Prop.
  Lemma _comm_link_imp_compile
        src1 src2 srcl tgt1 tgt2 tgtl
        (COMP1: compile src1 = OK tgt1)
        (COMP2: compile src2 = OK tgt2)
        (LINKSRC: link_imp src1 src2 = Some srcl)
        (LINKTGT: link tgt1 tgt2 = Some tgtl)
    :
      <<COMPL: compile srcl = OK tgtl>>.
  Proof.
    apply link_prog_inv in LINKTGT. unfold prog_defmap in *; ss.
    unfold compile in *. des_ifs_safe; ss. des. clear LINKTGT. des_ifs_safe.
    rename l0 into NOREPET1, l into NOREPET2.
    assert (NOREPET: Coqlib.list_norepet_dec dec (List.map fst (compile_gdefs srcl))).
    { admit "ez". }
    des_ifs_safe. clear NOREPET. rename l into NOREPET.
    red. f_equal. f_equal; ss.
    2:{ unfold link_imp in LINKSRC. des_ifs_safe. ss. unfold l_publicL. apply map_app. }
    apply PTree.elements_extensional. i.
    erewrite PTree.gcombine; ss. rewrite ! PTree_Properties.of_list_elements.

    assert (LINKTGTP : forall (id : positive) (gd1 gd2 : globdef fundef ()),
               (PTree_Properties.of_list (compile_gdefs src1)) ! id = Some gd1 ->
               (PTree_Properties.of_list (compile_gdefs src2)) ! id = Some gd2 ->
               In id (List.map s2p (publicL src1)) /\
               In id (List.map s2p (publicL src2)) /\ (exists gd : globdef fundef (), link gd1 gd2 = Some gd)).
    { i.
      rewrite <- PTree_Properties.of_list_elements in H.
      rewrite <- PTree_Properties.of_list_elements in H0.
      auto.
    }
    clear LINKTGT0. sym. rename i into id.

    match goal with
    | [ |- link_prog_merge ?ak ?bk = ?lk ] => destruct ak eqn:AK; destruct bk eqn:BK; destruct lk eqn:LK; ss; clarify; eauto
    end.

    - rename g into gd1, g0 into gd2, g1 into gdl. clear LINKTGTP.
      apply PTree_Properties.in_of_list in AK.
      apply PTree_Properties.in_of_list in BK.
      apply PTree_Properties.in_of_list in LK.
      admit "case analysis for each gd".

    - hexploit LINKTGTP; eauto. i; des. clear H H0.
      admit "case analysis for each gd, should be tied with above".

    - apply PTree_Properties.in_of_list in AK. apply PTree_Properties.in_of_list in LK.
      destruct (classic (In id (List.map fst (compile_gdefs src2)))).
      { apply PTree_Properties.of_list_dom in H. des. clarify. }
      clear BK; rename H into BK.
      admit "name only in a".

    - apply PTree_Properties.in_of_list in AK.
      destruct (classic (In id (List.map fst (compile_gdefs src2)))).
      { apply PTree_Properties.of_list_dom in H. des. clarify. }
      clear BK; rename H into BK.
      admit "name only in a, linked should have a's def".

    - admit "sym".
    - admit "sym".
    - admit "should not exists".
  Qed.





  Lemma _comm_link_imp_compile_exists_link
        src1 src2 srcl tgt1 tgt2
        (COMP1: compile src1 = OK tgt1)
        (COMP2: compile src2 = OK tgt2)
        (LINKSRC: link_imp src1 src2 = Some srcl)
        
    :
      (exists tgtl, <<LINKTGT: link tgt1 tgt2 = Some tgtl>>).
  Proof.
    hexploit (link_prog_succeeds tgt1 tgt2).
    { admit "ez". }
    { i. apply PTree_Properties.in_of_list in H. apply PTree_Properties.in_of_list in H0. rename H into IN1, H0 into IN2.
      split.
      { admit "true if lifted imp prog". }
      split.
      { admit "true if lifted". }
      destruct gd1; destruct gd2.
      - destruct f; destruct f0.
        + admit "if/if, contra".
        + admit "if/ef, init_g, c_sys case".
        + admit "ef/if, init_g, c_sys case".
        + admit "init_g, c_sys..., reverse from prog_def".

      - admit "link fail, contra".

      - admit "sym".

      - admit "reverse from prog_defs, & characterize int/ext".
    }
    i. match goal with | [H: link_prog _ _ = Some ?_tgtl |- _ ] => exists _tgtl end. ss.
  Qed.

  (* link_def *)
  (* link_fundef *)
  (* link_vardef *)
  (* link_varinit *)

  Lemma _comm_link_imp_compile_exists
        src1 src2 srcl tgt1 tgt2
        (COMP1: compile src1 = OK tgt1)
        (COMP2: compile src2 = OK tgt2)
        (LINKSRC: link_imp src1 src2 = Some srcl)
        
    :
      (exists tgtl, (<<LINKTGT: link tgt1 tgt2 = Some tgtl>>) /\ (<<COMP: compile srcl = OK tgtl>>)).
  Proof.
    hexploit _comm_link_imp_compile_exists_link.
    3: eapply LINKSRC.
    1,2: eauto.
    i. des. exists tgtl. split; auto. eapply _comm_link_imp_compile.
    3,4: eauto.
    1,2: eauto.
  Qed.



  Fixpoint compile_imps (src_list : list Imp.programL) :=
    match src_list with
    | [] => Some []
    | src :: srcs =>
      match compile src with
      | OK tgt =>
        match compile_imps srcs with
        | Some tgts => Some (tgt :: tgts)
        | _ => None
        end
      | _ => None
      end
    end.

  (* Inductive compile_list : *)
  (*   list programL -> list (Csharpminor.program) -> Prop := *)
  (* | compile_nil : *)
  (*     compile_list [] [] *)
  (* | compile_head *)
  (*     src_h src_t tgt_h tgt_t *)
  (*     (COMPH: compile src_h = OK tgt_h) *)
  (*     (COMPT: compile_list src_t tgt_t) *)
  (*   : *)
  (*     <<COMPLIST: compile_list (src_h :: src_t) (tgt_h :: tgt_t)>>. *)
  Definition link_csm_list (tgt_list : list (Csharpminor.program)) :=
    match tgt_list with
    | [] => None
    | tgt_h :: tgt_t =>
      fold_left_option link_prog tgt_t (Some tgt_h)
    end.

  (* Lemma comm_link_imp_compile *)
  (*       src_list srcl tgt_list tgtl *)
  (*       (COMPL: compile_list src_list tgt_list) *)
  (*       (LINKSRC: link_imp_list src_list = Some srcl) *)
  (*       (LINKTGT: link_csm_list tgt_list = Some tgtl) *)
  (*   : *)
  (*     compile srcl = OK tgtl. *)
  (* Proof. *)
  (*   i. destruct src_list; destruct tgt_list; ss; clarify. *)
  (*   inv COMPL; clarify. *)
  (*   generalize dependent srcl. generalize dependent tgtl. *)
  (*   generalize dependent p. generalize dependent p0. *)
  (*   induction COMPT; i; ss; clarify. *)
  (*   destruct (link_prog p0 tgt_h) eqn:LPt; ss; clarify. *)
  (*   2:{ rewrite fold_left_option_None in LINKTGT; clarify. } *)
  (*   destruct (link_imp p src_h) eqn:LPs; ss; clarify. *)
  (*   2:{ rewrite fold_left_option_None in LINKSRC; clarify. } *)
  (*   eapply IHCOMPT. *)
  (*   2: apply LINKTGT. *)
  (*   2: apply LINKSRC. *)
  (*   eapply _comm_link_imp_compile. *)
  (*   3: apply LPs. *)
  (*   3: apply LPt. *)
  (*   auto. auto. *)
  (* Qed. *)

End PROOFRIGHT.




Section PROOFLINK.

  (* Definition src_initial_state (src : ModL.t) := *)
  (*   (ModL.compile src).(initial_state). *)

  (* Theorem compile_behavior_improves *)
  (*         (src_list : list Imp.program) srcl tgt_list tgtl srcst tgtst *)
  (*         (COMP: let src_list_lift := List.map Imp.lift src_list in *)
  (*                compile_list src_list_lift tgt_list) *)
  (*         (LINKSRC: let src_list_mod := List.map ImpMod.get_mod src_list in *)
  (*                   Mod.add_list (Mem :: src_list_mod) = srcl) *)
  (*         (LINKTGT: link_csm_list tgt_list = Some tgtl) *)
  (*         (SINIT: srcst = src_initial_state srcl) *)
  (*         (TINIT: Csharpminor.initial_state tgtl tgtst) *)
  (*   : *)
  (*     <<IMPROVES: @improves2 _ (Csharpminor.semantics tgtl) srcst tgtst>>. *)
  (* Proof. *)
  (* Admitted. *)

End PROOFLINK.
