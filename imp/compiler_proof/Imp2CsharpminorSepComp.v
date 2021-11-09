From compcert Require Import Maps Globalenvs Smallstep AST Integers Events Behaviors Errors Memory Csharpminor Linking.
Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
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
Require Import Imp2CsharpminorLenv.
Require Import Imp2CsharpminorMem.
Require Import Imp2CsharpminorLink.
Require Import Imp2CsharpminorSim.

Set Implicit Arguments.

Section PROOFLEFT.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

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
    destruct src_list as [ | src0 src_list ]; ss; clarify.
    move src_list before builtins. revert_until builtins. induction src_list; i; ss; clarify.
    { rewrite ModL.add_empty_r. ss. }
    red. des_ifs; ss; clarify.
    hexploit IHsrc_list.
    { eapply Heq. }
    i. erewrite H. clear H. eapply _comm_link_imp_link_mod; eauto.
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
  Context `{builtins : builtinsTy}.

  (* Proving the right arrow of the diagram *)

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
    assert (NOREPET: Coqlib.list_norepet (List.map fst (compile_gdefs srcl))).
    { hexploit link_then_unique_ids; eauto. }
    des_ifs_safe. clear l.
    red. f_equal. f_equal; ss.
    2:{ unfold link_imp in LINKSRC. des_ifs_safe. ss. unfold l_publicL. rewrite <- app_assoc. f_equal.
        rewrite map_app. f_equal; ss. rewrite map_app. f_equal; ss. setoid_rewrite List.map_map. ss. }
    apply PTree.elements_extensional. i.
    erewrite PTree.gcombine; ss. rewrite ! PTree_Properties.of_list_elements.

    assert (LINKTGTP : forall (id : positive) (gd1 gd2 : globdef fundef ()),
               (PTree_Properties.of_list (compile_gdefs src1)) ! id = Some gd1 ->
               (PTree_Properties.of_list (compile_gdefs src2)) ! id = Some gd2 ->
               In id (List.map (s2p ∘ fst) init_g0 ++ List.map s2p (publicL src1)) /\
               In id (List.map (s2p ∘ fst) init_g0 ++ List.map s2p (publicL src2)) /\
               (exists gd : globdef fundef (), link gd1 gd2 = Some gd)).
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
      hexploit link_then_exists_gd.
      3: eapply LINKSRC.
      1,2,3,4: eauto.
      i. des.
      hexploit PTree_Properties.of_list_norepet.
      { eapply NOREPET. }
      { eapply INL. }
      i. clarify.

    - hexploit LINKTGTP; eauto. i; des. clear H H0.
      destruct (classic (In id (List.map fst (compile_gdefs srcl)))).
      { apply PTree_Properties.of_list_dom in H. des. clarify. }
      clear LK; rename H into LK.
      apply PTree_Properties.in_of_list in AK. apply PTree_Properties.in_of_list in BK.
      hexploit link_then_exists_gd.
      3: eapply LINKSRC.
      1,2,3,4: eauto.
      i. des.
      apply (in_map fst) in INL. ss.

    - apply PTree_Properties.in_of_list in AK. apply PTree_Properties.in_of_list in LK.
      destruct (classic (In id (List.map fst (compile_gdefs src2)))).
      { apply PTree_Properties.of_list_dom in H. des. clarify. }
      clear BK; rename H into BK.
      eapply in_tgtl_then_in_some in LK; eauto. des.
      + hexploit compile_gdefs_unique_defs. eapply NOREPET1. eapply AK. eapply IN1. i; clarify; ss.
      + apply (in_map fst) in BK0. ss; clarify.

    - apply PTree_Properties.in_of_list in AK.
      destruct (classic (In id (List.map fst (compile_gdefs src2)))).
      { apply PTree_Properties.of_list_dom in H. des. clarify. }
      clear BK; rename H into BK.
      destruct (classic (In id (List.map fst (compile_gdefs srcl)))).
      { apply PTree_Properties.of_list_dom in H. des. clarify. }
      clear LK; rename H into LK.
      exfalso.
      hexploit in_left_in_link; eauto. i. apply (in_map fst) in H. ss.

    - apply PTree_Properties.in_of_list in BK. apply PTree_Properties.in_of_list in LK.
      destruct (classic (In id (List.map fst (compile_gdefs src1)))).
      { apply PTree_Properties.of_list_dom in H. des. clarify. }
      clear AK; rename H into AK.
      eapply in_tgtl_then_in_some in LK; eauto. des.
      + apply (in_map fst) in IN1. ss; clarify.
      + hexploit compile_gdefs_unique_defs. eapply NOREPET2. eapply BK. eapply BK0. i; clarify; ss.

    - apply PTree_Properties.in_of_list in BK.
      destruct (classic (In id (List.map fst (compile_gdefs src1)))).
      { apply PTree_Properties.of_list_dom in H. des. clarify. }
      clear AK; rename H into AK.
      destruct (classic (In id (List.map fst (compile_gdefs srcl)))).
      { apply PTree_Properties.of_list_dom in H. des. clarify. }
      clear LK; rename H into LK.
      exfalso.
      hexploit in_right_in_link; eauto. i. apply (in_map fst) in H. ss.

    - apply PTree_Properties.in_of_list in LK.
      destruct (classic (In id (List.map fst (compile_gdefs src1)))).
      { apply PTree_Properties.of_list_dom in H. des. clarify. }
      clear AK; rename H into AK.
      destruct (classic (In id (List.map fst (compile_gdefs src2)))).
      { apply PTree_Properties.of_list_dom in H. des. clarify. }
      clear BK; rename H into BK.
      exfalso. eapply in_tgtl_then_in_some in LK; eauto. des.
      + apply (in_map fst) in IN1. ss.
      + apply (in_map fst) in BK0. ss.

  Qed.

  Lemma comm_link_imp_compile
        (srcs: list Imp.programL) srcl
        tgts tgtl
        (COMPS: Forall2 (fun src tgt => compile src = OK tgt) srcs (nlist2list tgts))
        (LINKSRC: link_imp_list srcs = Some srcl)
        (LINKTGT: link_list tgts = Some tgtl)
    :
      compile srcl = OK tgtl.
  Proof.
    destruct srcs as [| src0 srcs]; ss; clarify.
    inv COMPS; clarify. rename tgts into ntgts, y into tgt0, l' into tgts, H2 into COMP0, H3 into COMPS.
    depgen srcl. depgen tgtl. depgen src0. depgen tgt0. depgen ntgts.
    induction COMPS; i; ss; clarify.
    { destruct ntgts; ss; clarify. sym in H0. apply n2l_not_nil in H0. clarify. }
    rename l into srcs, l' into tgts. des_ifs. sym in H1. hexploit (n2l_cons_exists ntgts).
    { eapply H1. }
    i. des. rewrite H2 in LINKTGT. ss. des_ifs.
    hexploit IHCOMPS.
    4: eapply Heq.
    2: eapply H.
    1: sym; eapply H0.
    1: eapply Heq0.
    i. eapply _comm_link_imp_compile with (tgt1:=tgt0) (tgt2:=p0); eauto.
  Qed.


  Definition wf_public (src: Imp.programL) :=
    forall id, In id (name1 (compile_gdefs src)) -> In id (List.map (s2p ∘ fst) init_g0 ++ List.map s2p (publicL src)).

  Lemma lifted_then_wf_public :
    forall (src: Imp.program), <<WFLIFT: wf_public (lift src)>>.
  Proof.
    i. red. unfold lift in *. unfold wf_public. ii; ss. apply Coqlib.list_in_map_inv in H. des. destruct x; ss; clarify.
    rename i into id, g into gd. apply decomp_gdefs in H0; ss. des; clarify; eauto.
    - apply in_bts_in_init_g in BTS1. des.
      Local Transparent init_g. unfold init_g in BTS1. Local Opaque init_g.
      destruct fd; ss; clarify. rewrite in_app_iff; left. apply (in_map fst) in BTS1. ss.
      rewrite List.map_map in BTS1.
      match goal with
      | [ BTS1: In _ ?l1 |- In _ ?l2 ] => replace l2 with l1; ss; auto end.
      apply map_ext. i. destruct a; ss.
    - Local Transparent init_g0. unfold init_g0. Local Opaque init_g0.
      rewrite map_app. rewrite in_app_iff; left. apply in_app_iff; right. ss. eauto.
    - Local Transparent init_g0. unfold init_g0. Local Opaque init_g0.
      rewrite map_app. rewrite in_app_iff; left. apply in_app_iff; right. ss. eauto.
    - rewrite in_app_iff; right. unfold public. repeat rewrite map_app. repeat rewrite in_app_iff.
      left. rewrite List.map_map. apply (in_map (s2p ∘ fst)) in SYS0. destruct fd; ss; clarify.
    - rewrite in_app_iff; right. unfold public. repeat rewrite map_app. repeat rewrite in_app_iff.
      do 2 right; left. rewrite List.map_map. apply (in_map (s2p ∘ fst)) in EFS0. destruct fd; ss; clarify.
    - rewrite in_app_iff; right. unfold public. repeat rewrite map_app. repeat rewrite in_app_iff.
      do 1 right; left. apply (in_map s2p) in EVS0. unfold compile_eVar in *. clarify.
    - rewrite in_app_iff; right. unfold public. repeat rewrite map_app. repeat rewrite in_app_iff.
      do 4 right. destruct fd as [mn [fn ff]]; ss; clarify. apply (in_map (s2p ∘ fst ∘ snd)) in IFS0; ss.
      rewrite List.map_map in IFS0. ss. rewrite List.map_map. auto.
    - rewrite in_app_iff; right. unfold public. repeat rewrite map_app. repeat rewrite in_app_iff.
      do 3 right; left. destruct vd; ss; clarify. apply (in_map (s2p ∘ fst)) in IVS0. ss.
      rewrite List.map_map. ss.
  Qed.

  Lemma link_two_wf_public
        src1 src2 srcl
        (WFP1: wf_public src1)
        (WFP2: wf_public src2)
        (LINKSRC: link_imp src1 src2 = Some srcl)
    :
      <<WFPL: wf_public srcl>>.
  Proof.
    red. unfold wf_public in *. ii. apply Coqlib.list_in_map_inv in H. des. destruct x as [name def]; ss; clarify.
    hexploit in_tgtl_then_in_some; eauto. i.
    unfold link_imp in LINKSRC. des_ifs; ss. clear H0. unfold l_publicL.
    rewrite map_app. rewrite app_assoc. apply in_app_iff.
    des.
    { left. apply (in_map fst) in IN1. ss. apply WFP1 in IN1. ss. }
    { right. apply (in_map fst) in BK. ss. apply WFP2 in BK. rewrite <- List.map_map in BK.
      rewrite <- map_app in BK. ss. }
  Qed.

  Lemma linked_list_wf_public
        (srcs: list Imp.programL) srcl
        (WFPUBS: Forall wf_public srcs)
        (LINKED: link_imp_list srcs = Some srcl)
    :
      <<WFLINK: wf_public srcl>>.
  Proof.
    red. destruct srcs as [| src0 srcs]; ss; clarify.
    depgen src0. depgen srcl. induction srcs; i; ss; clarify.
    { inv WFPUBS. ss. }
    rename a into src1. des_ifs; ss; clarify.
    hexploit IHsrcs.
    2:{ eapply Heq. }
    { inv WFPUBS. auto. }
    i. eapply link_two_wf_public with (src1:=src0) (src2:=p); eauto.
    inv WFPUBS; auto.
  Qed.

  Lemma _comm_link_imp_compile_exists_link
        src1 src2 tgt1 tgt2
        (WFP1: wf_public src1)
        (WFP2: wf_public src2)
        (COMP1: compile src1 = OK tgt1)
        (COMP2: compile src2 = OK tgt2)
        (LINKSRC: exists srcl, link_imp src1 src2 = Some srcl)
    :
      (exists tgtl, <<LINKTGT: link tgt1 tgt2 = Some tgtl>>).
  Proof.
    des.
    hexploit (link_prog_succeeds tgt1 tgt2).
    { unfold compile in *. des_ifs. }
    { i. apply PTree_Properties.in_of_list in H. apply PTree_Properties.in_of_list in H0. rename H into IN1, H0 into IN2.
      unfold compile in *. des_ifs. ss. rename l0 into NOREPET1, l into NOREPET2.
      hexploit perm_elements_PTree_norepeat_in_in.
      { eapply NOREPET1. }
      i. apply H in IN1. clear H.
      hexploit perm_elements_PTree_norepeat_in_in.
      { eapply NOREPET2. }
      i. apply H in IN2. clear H.
      repeat split.
      { unfold wf_public in WFP1. apply (in_map fst) in IN1. eauto. }
      { unfold wf_public in WFP2. apply (in_map fst) in IN2. eauto. }
      hexploit link_then_exists_gd.
      3: eapply LINKSRC.
      all: eauto.
      i. des. ii. clarify.
    }
    i. match goal with | [H: link_prog _ _ = Some ?_tgtl |- _ ] => exists _tgtl end. ss.
  Qed.

  Lemma comm_link_imp_compile_exists_link
        (srcs: list Imp.programL) tgts
        (WFPS: Forall wf_public srcs)
        (COMPS: Forall2 (fun src tgt => compile src = OK tgt) srcs (nlist2list tgts))
        (LINKSRC: exists srcl, link_imp_list srcs = Some srcl)
    :
      exists tgtl, <<LINKTGT: link_list tgts = Some tgtl>>.
  Proof.
    des.
    destruct srcs as [| src0 srcs]; ss; clarify.
    inv COMPS; clarify. rename tgts into ntgts, y into tgt0, l' into tgts, H2 into COMP0, H3 into COMPS.
    depgen srcl. depgen src0. depgen tgt0. depgen ntgts.
    induction COMPS; i; ss; clarify.
    { destruct ntgts; ss; clarify.
      { exists p; auto. }
      sym in H0. apply n2l_not_nil in H0; clarify. }
    rename l into srcs, l' into tgts. des_ifs. sym in H1. hexploit (n2l_cons_exists ntgts).
    { eapply H1. }
    i. des.
    hexploit IHCOMPS.
    4: eapply Heq.
    2:{ inv WFPS. auto. }
    1: sym; eapply H0.
    1: eapply H.
    i. des. rewrite H2. ss. rewrite LINKTGT.
    eapply _comm_link_imp_compile_exists_link with (tgt1:=tgt0) (tgt2:=tgtl); eauto.
    { inv WFPS. auto. }
    { rename p into src2. eapply linked_list_wf_public.
      2:{ instantiate (1:= x :: srcs). ss. }
      inv WFPS; auto. }
    rename p into src2. eapply comm_link_imp_compile.
    2:{ instantiate (1:= x :: srcs). ss. }
    all: eauto.
    rewrite H0. econs; eauto.
  Qed.

  Lemma _comm_link_imp_compile_exists
        src1 src2 srcl tgt1 tgt2
        (WFP1: wf_public src1)
        (WFP2: wf_public src2)
        (COMP1: compile src1 = OK tgt1)
        (COMP2: compile src2 = OK tgt2)
        (LINKSRC: link_imp src1 src2 = Some srcl)

    :
      (exists tgtl, (<<LINKTGT: link tgt1 tgt2 = Some tgtl>>) /\ (<<COMP: compile srcl = OK tgtl>>)).
  Proof.
    hexploit _comm_link_imp_compile_exists_link.
    5:{ exists srcl. eapply LINKSRC. }
    1,2,3,4: eauto.
    i. des. exists tgtl. split; auto. eapply _comm_link_imp_compile.
    3,4: eauto.
    1,2: eauto.
  Qed.

  Lemma comm_link_imp_compile_exists
        (srcs: list Imp.programL) srcl
        tgts
        (WFPS: Forall wf_public srcs)
        (COMPS: Forall2 (fun src tgt => compile src = OK tgt) srcs (nlist2list tgts))
        (LINKSRC: link_imp_list srcs = Some srcl)
    :
      (exists tgtl, (<<LINKTGT: link_list tgts = Some tgtl>>) /\ (<<COMP: compile srcl = OK tgtl>>)).
  Proof.
    hexploit comm_link_imp_compile_exists_link.
    3:{ exists srcl. eapply LINKSRC. }
    all: eauto.
    i. des. exists tgtl. split; auto. eapply comm_link_imp_compile; eauto.
  Qed.

  Theorem right_arrow
          (srcs: list Imp.program) srcl
          tgts
          (COMPS: Forall2 (fun src tgt => compile (lift src) = OK tgt) srcs (nlist2list tgts))
          (LINKSRC: link_imps srcs = Some srcl)
    :
      (exists tgtl, (<<LINKTGT: link_list tgts = Some tgtl>>) /\ (<<COMP: compile srcl = OK tgtl>>)).
  Proof.
    eapply comm_link_imp_compile_exists.
    3: eapply LINKSRC.
    - clear. induction srcs; ss; clarify. econs; eauto. apply lifted_then_wf_public.
    - depgen COMPS. clear. i. induction COMPS; ss; clarify. econs; eauto.
  Qed.

End PROOFRIGHT.





Section PROOFSINGLE.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Create HintDb ord_step2.
  Hint Resolve Nat.lt_succ_diag_r OrdArith.lt_from_nat OrdArith.lt_add_r: ord_step2.
  Hint Extern 1000 => lia: ord_step2.
  Ltac ord_step2 := eauto with ord_step2.

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); econs 3; ss; clarify; eexists; exists (ModSemL.step_tau _); eexists; split; [ord_step2|auto].

  (* Ltac sim_triggerUB := unfold triggerUB; (try sim_red); econs 5; i; ss; auto; *)
  (*                       dependent destruction STEP; try (irw in x; clarify; fail). *)
  Ltac solve_ub := des; irw in H; dependent destruction H; clarify.
  Ltac sim_triggerUB := (try rename H into HH); pfold; ss; unfold triggerUB; try sim_red; econs 5; i; ss; auto;
                        [solve_ub | dependent destruction STEP; try (irw in x; clarify; fail)].

  Ltac dtm H H0 := eapply angelic_step in H; eapply angelic_step in H0; des; rewrite H; rewrite H0; ss.

  Definition imp_sem (src : Imp.programL) := compile_val (ModL.add (Mod.lift (Mem (fun _ => false))) (ImpMod.get_modL src)).

  Definition imp_initial_state (src : Imp.programL) := (imp_sem src).(initial_state).

  Theorem single_compile_behavior_improves
          (src: Imp.programL) (tgt: Csharpminor.program) srcst tgtst
          (WFPROG: incl (name1 src.(defsL)) ((name1 src.(prog_varsL)) ++ (name2 src.(prog_funsL))))
          (WFPROG3: forall blk name,
              let modl := ModL.add (Mod.lift (Mem (fun _ => false))) (ImpMod.get_modL src) in
              let ge := (Sk.load_skenv (Sk.sort modl.(ModL.sk))) in
              (ge.(SkEnv.blk2id) blk = Some name) -> call_ban name = false)
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
    instantiate (1:= ((100 + max_fuel) + 100 + Ord.omega + 120)%ord).
    red. unfold imp_initial_state in *. ss; clarify. inv TINIT.
    rename m0 into tm, ge into tge, H into TMINIT, H0 into TMAIN1, H1 into TMAIN2, H2 into TSIGMAIN, b into tb, f into tmain.
    assert (COMP0: Imp2Csharpminor.compile src = OK tgt); auto. move COMP0 before tgt.
    unfold compile in COMP. des_ifs.
    match goal with | [ COMP0: compile _ = OK ?_tgt |- _ ] => set (tgt:=_tgt) in * end.
    rename l into NOREPET.
    unfold ModSemL.initial_itr.
    pfold. econs 5; eauto. unfold assume. ss.
    { grind. dtm H H0. }
    unfold assume. grind. eapply angelic_step in STEP. des; clarify.
    eexists; split; [ord_step2|auto].

    left. unfold ITree.map. sim_red. rewrite ! Sk.add_unit_l.
    set (sge:=Sk.load_skenv (Sk.sort (defsL src))) in *.
    destruct (alist_find "main" (List.map (fun '(mn, (fn, f)) => (fn, transl_all mn (T:=_) ∘ cfunU (eval_imp sge f))) (prog_funsL src)))
             eqn:FOUNDMAIN; ss; grind.
    2:{ unfold triggerUB. ired. pfold; econs 5; ss.
        { i. solve_ub. } { i. dependent destruction STEP; irw in x; ss. injection x. i. simpl_depind. ss. }
    }
    repeat match goal with | [ H : false = false |- _ ] => clear H end.
    rewrite alist_find_find_some in FOUNDMAIN. rewrite find_map in FOUNDMAIN. uo; des_ifs; ss.
    rename s into mn, f into smain, Heq into SFOUND. apply find_some in SFOUND. des. ss. clear SFOUND0.

    set (tgds:=compile_gdefs src) in *.
    hexploit in_compile_gdefs_ifuns; eauto. i. rename H into INFMAIN.
    hexploit in_tgt_prog_defs_ifuns; eauto. i. rename H into INFMAINTGT.
    hexploit tgt_genv_find_def_by_blk; eauto. i. rename H into TGTMAIN. ss; clarify.
    match goal with [H: Genv.find_def _ _ = Some (Gfun (Internal ?tf)) |- _ ] => set (tmainf:=tf) in * end.
    unfold cfunU. rewrite Any.upcast_downcast. grind. rewrite unfold_eval_imp_only.
    sim_red.
    des_ifs.
    2,3,4: sim_triggerUB.
    rename n into WF_MAIN.

    grind; sim_red.
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

    unfold ModL.wf in WF. des.

    pfold. econs 6; ss; eauto. eexists. eexists.
    { eapply step_seq. }
    eexists. exists (ModSemL.step_tau _). exists ((100 + max_fuel) + 100 + Ord.omega + 100)%ord. left.
    rewrite interp_imp_bind. grind. sim_red.
    assert (MATCHGE: match_ge src (Sk.load_skenv (Sk.sort (ModL.sk (ModL.add (Mem (fun _ => false)) (ImpMod.get_modL src))))) (Genv.globalenv tgt)).
    { econs. i. simpl in H. rewrite Sk.add_unit_l in H.
      unfold map_blk. rewrite COMP0. hexploit Sk.env_found_range; eauto. i. unfold src_init_nb, int_len.
      rewrite <- sksort_same_len in H0. ss. unfold sk_len. des.
      hexploit (Sk.sort_wf SK). i. rewrite Sk.add_unit_l in H1.
      apply Sk.load_skenv_wf in H1.
      apply H1 in H. unfold get_sge. ss. rewrite H. unfold get_tge. des_ifs; try lia.
      hexploit found_in_src_in_tgt; eauto. i. des. unfold get_tge in H2. clarify.
    }
    ss. rewrite Sk.add_unit_l in MATCHGE. rewrite Sk.add_unit_l in WF0.

    unfold imp_sem in *.
    eapply match_states_sim; eauto.
    { apply map_blk_after_init. }
    { apply map_blk_inj. }
    ss. rewrite Sk.add_unit_l.
    match goal with
    | [ |- match_states ?_ge ?_ms _ _ _ ] => replace _ge with sge; auto
    end.
    match goal with
    | [ |- match_states ?_ge ?_ms _ _ _ ] => set (ms:=_ms) in *
    end.
    ss.
    econs; eauto.
    { eapply init_lenv_match; eauto. rewrite map_app. ss. }
    { clarify. }
    { econs; ss.
      { unfold src_init_nb, sk_len. rewrite <- sksort_same_len. lia. }
      { apply Genv.init_mem_genv_next in TMINIT. rewrite <- TMINIT. unfold Genv.globalenv. ss.
        rewrite Genv.genv_next_add_globals. ss. rewrite Genv_advance_next_length. ss.
        rewrite length_elements_PTree_norepet; eauto. rewrite map_blk_after_init; eauto.
        2:{ unfold src_init_nb, sk_len. rewrite <- sksort_same_len. lia. }
        unfold ext_len. subst tgds.
        rewrite Pos2Nat.inj_1. rewrite Nat.add_1_r. rewrite <- Pos.of_nat_succ. f_equal.
        rewrite gdefs_preserves_length. repeat rewrite <- Nat.add_assoc. do 3 f_equal.
        unfold Sk.wf in SK. ss.
        rewrite Sk.add_unit_l in SK.
        hexploit wfprog_defsL_length; eauto. i. des.
        unfold sk_len in *.
        match goal with | [ |- _ = ?x ] => replace x with (int_len src) end.
        { unfold int_len. ss. }
        rewrite <- sksort_same_len. sym. apply Nat.sub_add. auto.
      }
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
        replace i0 with ((fun '(p, (le, _)) => itree_of_imp_ret sge le ms mn (p)) : (_ * (lenv * val)) -> _);
          replace s0 with [exit_stmt]; eauto
      end.
      { econs 1. }
      extensionality x. unfold itree_of_imp_ret, itree_of_imp_cont. grind. destruct p0. rewrite interp_imp_expr_Var. grind. }
    { ss.
      match goal with
      | [ |- match_stack _ _ _ _ ?i0 ?s0 ] =>
        replace i0 with ((itree_of_imp_pop_bottom ms mn) : (_ * (lenv * val)) -> _);
          replace s0 with (Some ret_call_main); eauto
      end.
      { econs 1. }
      extensionality x. unfold itree_of_imp_pop_bottom. grind. sim_red. Red.prw ltac:(_red_gen) 1 0. ss.
    }
  Qed.

  Theorem single_compile_program_improves
          (src: Imp.programL) (tgt: Csharpminor.program)
          (WFPROG: incl (name1 src.(defsL)) ((name1 src.(prog_varsL)) ++ (name2 src.(prog_funsL))))
          (WFPROG3: forall blk name,
              let modl := ModL.add (Mod.lift (Mem (fun _ => false))) (ImpMod.get_modL src) in
              let ge := (Sk.load_skenv (Sk.sort modl.(ModL.sk))) in
              (ge.(SkEnv.blk2id) blk = Some name) -> call_ban name = false)
          (WFPROG2 : forall gn gv, In (gn, Sk.Gvar gv) (Sk.sort (defsL src)) -> In (gn, gv) (prog_varsL src))
          (COMP: Imp2Csharpminor.compile src = OK tgt)
    :
      <<IMPROVES: improves2_program (imp_sem src) (Csharpminor.semantics tgt)>>.
  Proof.
    red. unfold improves2_program. i. inv BEH.
    { eapply single_compile_behavior_improves; eauto. }
    (* initiall wrong case, for us only when main is not found *)
    exists (Tr.ub). split; red; eauto.
    2:{ pfold. econs 4; eauto.
        - ss.
        - unfold behavior_prefix. exists (Goes_wrong E0). ss.
    }
    rename H into NOINIT.
    unfold imp_sem in *. ss. unfold ModSemL.initial_itr.
    pfold. econs 6; ss; eauto.
    unfold Beh.inter. ss. unfold assume. grind.
    apply ModSemL.step_trigger_take_iff in STEP. des. clarify. split; eauto.
    red. unfold ITree.map; ss.
    unfold unwrapU. des_ifs.
    (* main do not exists, ub *)
    2:{ sim_red. unfold triggerUB. grind. econs 6; ss. grind. ss. apply ModSemL.step_trigger_take_iff in STEP. des. clarify. }

    (* found main, contradiction *)
    exfalso.
    rename Heq into FSEM.
    grind. rewrite alist_find_find_some in FSEM. rewrite find_map in FSEM.
    match goal with
    | [ FSEM: o_map (?a) _ = _ |- _ ] => destruct a eqn:FOUND; ss; clarify
    end.
    destruct p as [mn [fn ff]]; ss; clarify.
    rewrite Sk.add_unit_l in FOUND.
    eapply found_imp_function in FOUND. des; clarify.
    hexploit in_tgt_prog_defs_ifuns; eauto. i.
    des. rename H into COMPF. clear FOUND.
    assert (COMPF2: In (compile_iFun (mn, ("main", ff))) (prog_defs tgt)); auto.
    eapply Globalenvs.Genv.find_symbol_exists in COMPF.
    destruct COMPF as [b TGTFG].
    assert (TGTGFIND: Globalenvs.Genv.find_def (Globalenvs.Genv.globalenv tgt) b = Some (snd (compile_iFun (mn, ("main", ff))))).
    { hexploit tgt_genv_find_def_by_blk; eauto. }

    unfold compile in COMP. des_ifs.
    match goal with [ H: Genv.find_symbol (Genv.globalenv ?_tgt) _ = _ |- _ ] => set (tgt:=_tgt) in * end.
    hexploit (Genv.init_mem_exists tgt); eauto.
    { i. subst tgt; ss. hexploit perm_elements_PTree_norepeat_in_in; eauto.
      i. apply H0 in H. clear H0. apply decomp_gdefs in H. des; ss; clarify; eauto.
      { unfold bts in BTS1. apply Coqlib.list_in_map_inv in BTS1. des. destruct fd; ss; clarify. destruct x0; ss; clarify. }
      { destruct fd. unfold compile_eFun in SYS; ss; clarify. }
      { destruct fd. unfold compile_eFun in EFS; ss; clarify. }
      { depgen EVS. clear. i. unfold compile_eVar in EVS. ss; clarify. }
      { depgen IFS. clear. i. destruct fd as [mn [fn ff]]. unfold compile_iFun in IFS; ss; clarify. }
      { depgen IVS. clear. i. unfold compile_iVar in IVS. destruct vd; ss; clarify. split; ss; eauto.
        - split; eauto. apply Z.divide_0_r.
        - i. des; eauto; clarify. }
    }
    i. des. unfold compile_iFun in *; ss; clarify.
    match goal with
    | [ H: Genv.find_def _ _ = Some (Gfun ?_fdef) |- _ ] => set (fdef:=_fdef) in * end.
    specialize NOINIT with (Callstate fdef [] Kstop m).
    apply NOINIT.
    econs; ss; eauto.
    unfold Genv.find_funct_ptr. rewrite TGTGFIND. ss.
  Qed.

End PROOFSINGLE.





Section PROOFLINK.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Definition wf_call_ban (src: Imp.programL) :=
    <<WFCB: forall blk name,
      let modl := ModL.add (Mem (fun _ => false)) (ImpMod.get_modL src) in
      let ge := Sk.load_skenv (Sk.sort (ModL.sk modl)) in
      SkEnv.blk2id ge blk = Some name -> call_ban name = false>>.

  Lemma lifted_wf_call_ban :
    forall (src: Imp.program), wf_call_ban (lift src).
  Proof.
    i. unfold wf_call_ban. ii. ss. apply Sk.in_env_in_sk in H. des. apply Sk.sort_incl_rev in H.
    unfold defs in H. rewrite Sk.add_unit_l in H.
    apply filter_In in H. des. ss. bsimpl. ss.
  Qed.

  Lemma linked_two_wf_call_ban :
    forall (src1 src2: Imp.programL) srcl
      (WF1: wf_call_ban src1)
      (WF2: wf_call_ban src2)
      (LINKED: link_imp src1 src2 = Some srcl),
      <<WFLINK: wf_call_ban srcl>>.
  Proof.
    ii. unfold wf_call_ban in *. ss. unfold link_imp in LINKED. des_ifs. ss. clear modl.
    unfold l_defsL in ge. subst ge. apply Sk.in_env_in_sk in H. des. apply Sk.sort_incl_rev in H.
    rewrite Sk.add_unit_l in H.
    apply in_app_iff in H. des.
    - apply Sk.sort_incl in H. apply Sk.in_sk_in_env in H. des. eapply WF1. eauto.
    - apply Sk.sort_incl in H. apply Sk.in_sk_in_env in H. des. eapply WF2. eauto.
  Qed.

  Lemma linked_list_wf_call_ban :
    forall (src_list: list Imp.programL) srcl
      (WFPROGS: Forall wf_call_ban src_list)
      (LINKED: link_imp_list src_list = Some srcl),
      <<WFLINK: wf_call_ban srcl>>.
  Proof.
    i. destruct src_list as [| src0 src_list]; ss; clarify.
    depgen src0. depgen srcl. induction src_list; i; ss; clarify.
    { inv WFPROGS. ss. }
    rename a into src1. des_ifs; ss; clarify. rename p into srct.
    hexploit IHsrc_list.
    2:{ eapply Heq. }
    { inv WFPROGS. ss. }
    i. red. eapply linked_two_wf_call_ban with (src1:=src0) (src2:=srct); eauto.
    inv WFPROGS. auto.
  Qed.

  Lemma linked_list_wf_lift_call_ban :
    forall (src_list: list Imp.program) srcl
      (LINKED: link_imps src_list = Some srcl),
      <<WFLINK: wf_call_ban srcl>>.
  Proof.
    i. unfold link_imps in LINKED. assert (WFPROGS: Forall wf_call_ban (List.map lift src_list)).
    { clear LINKED. clear srcl. induction src_list; ss; clarify. econs; auto. apply lifted_wf_call_ban. }
    hexploit linked_list_wf_call_ban; eauto.
  Qed.

  Definition imps_sem (srcs : list Imp.program) :=
    let srcs_mod := List.map ImpMod.get_mod srcs in compile_val (Mod.add_list ((Mem (fun _ => false)) :: srcs_mod)).

  Lemma compile_behavior_improves_compile
        (srcs : list Imp.program) (tgts : Coqlib.nlist Csharpminor.program)
        tgtl
        (COMP: Forall2 (fun src tgt => compile (lift src) = OK tgt) srcs (nlist2list tgts))
        (LINKSRC: exists srcl, link_imps srcs = Some srcl)
        (LINKTGT: link_list tgts = Some tgtl)
    :
      <<IMPROVES: improves2_program (imps_sem srcs) (Csharpminor.semantics tgtl)>>.
  Proof.
    des.
    i. unfold imps_sem.
    hexploit left_arrow; eauto.
    i. instantiate (1:=Mem (fun _ => false)) in H. rewrite H; clear H.
    hexploit right_arrow; eauto.
    i. des. clarify.
    hexploit linked_list_wf_lift; eauto. i. des. unfold wf_prog in H. des.
    hexploit linked_list_wf_lift_call_ban; eauto. i. des.
    eapply single_compile_program_improves; eauto.
  Qed.

  Lemma compile_behavior_improves_compile_exists
        (srcs : list Imp.program) (tgts : Coqlib.nlist Csharpminor.program)
        (COMP: Forall2 (fun src tgt => compile (lift src) = OK tgt) srcs (nlist2list tgts))
        (LINKSRC: exists srcl, link_imps srcs = Some srcl)
    :
      exists tgtl, (link_list tgts = Some tgtl).
  Proof.
    des. i.
    hexploit right_arrow; eauto.
    i. des. exists tgtl; eauto.
  Qed.

  Theorem compile_behavior_improves
          (srcs : list Imp.program) (tgts : Coqlib.nlist Csharpminor.program)
          (COMP: Forall2 (fun src tgt => compile_imp src = OK tgt) srcs tgts)
          (LINKSRC: exists srcl, link_imps srcs = Some srcl)
    :
      exists tgtl, ((link_list tgts = Some tgtl) /\
               (improves2_program (imps_sem srcs) (Csharpminor.semantics tgtl))).
  Proof.
    hexploit compile_behavior_improves_compile_exists; eauto. i. des. exists tgtl. split; eauto.
    eapply compile_behavior_improves_compile; eauto.
  Qed.

End PROOFLINK.
