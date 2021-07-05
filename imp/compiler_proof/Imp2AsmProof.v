From compcert Require Import
     Smallstep AST Events Behaviors Errors Csharpminor Linking Compiler Asm.
Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.
Require Import SimSTS2.
Require Import Imp2Csharpminor.
Require Import Csharpminor2Asm.

Require Import Imp2CsharpminorLink.
Require Import Imp2CsharpminorSepComp.
Require Import Imp2Asm.
Require Import Csharpminor2AsmProofs.

Set Implicit Arguments.


Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Lemma n2l_one {A} :
    forall (nl: @Coqlib.nlist A) (a: A)
      (ONE: [a] = nlist2list nl),
      nl = Coqlib.nbase a.
  Proof.
    i. depgen a. clear. induction nl; i; ss; clarify.
    sym in H0; apply n2l_not_nil in H0. clarify.
  Qed.

  Lemma compile_behavior_improves_exists
        (imps : list Imp.program) (asms : Coqlib.nlist Asm.program)
        (COMP: Forall2 (fun imp asm => compile_imp imp = OK asm) imps asms)
        (LINKSRC: exists impl, link_imps imps = Some impl)
    :
      exists asml, (link_list asms = Some asml).
  Proof.
    assert (CSM: exists csms, Forall2 (fun imp csm => Imp2Csharpminor.compile_imp imp = OK csm) imps (nlist2list csms)).
    { depgen LINKSRC. induction COMP; ss; clarify.
      { i. des. ss. }
      unfold compile_imp, compile in H. des_ifs.
      i. destruct l.
      { unfold link_imps in LINKSRC. ss. des. clarify. exists (Coqlib.nbase p); eauto. econs; eauto. }
      des.
      assert (exists srcl2, link_imps (p0 :: l) = Some srcl2).
      { unfold link_imps in LINKSRC. ss. des_ifs. exists p1. ss. }
      apply IHCOMP in H0. des. exists (Coqlib.ncons p csms). econs; eauto. }
    des. hexploit compile_behavior_improves; eauto. i.
    des. rename tgtl into csml, H into LINKCSM, H0 into IMP2.

    assert (C2A: Coqlib.nlist_forall2 (fun csm asm => transf_csharpminor_program csm = OK asm) csms asms).
    { clear IMP2. clear LINKCSM. depgen asms. depgen csms. clear. induction imps; i; ss; clarify.
      { inv CSM; inv COMP. sym in H; apply n2l_not_nil in H. clarify. }
      destruct csms as [| csm csms ].
      { inv CSM. inv H4. inv COMP. inv H4. apply n2l_one in H1. clarify. econs; eauto.
        unfold compile_imp, compile in H3. des_ifs.
        unfold Imp2Csharpminor.compile_imp in H2. rewrite H2 in Heq. clarify. }
      destruct asms as [| asm asms ].
      { inv COMP. inv H4. inv CSM. inv H5. sym in H; apply n2l_not_nil in H. clarify. }
      inv CSM; inv COMP. econs; eauto.
      unfold compile_imp, compile in H3. des_ifs.
      unfold Imp2Csharpminor.compile_imp in H2. rewrite H2 in Heq. clarify. }

    destruct (link_list asms) eqn:E. 
    - exists p; auto.
    - exfalso. 
      exploit separate_transf_csm_program_correct; eauto. intros (a & P & Q).
      congruence.
  Qed.

  Lemma compile_behavior_improves_if_exists
        (imps : list Imp.program) (asms : Coqlib.nlist Asm.program)
        asml
        (COMP: Forall2 (fun imp asm => compile_imp imp = OK asm) imps asms)
        (LINKSRC: exists impl, link_imps imps = Some impl)
        (LINKTGT: link_list asms = Some asml)
    :
      (improves2_program (imps_sem imps) (Asm.semantics asml)).
  Proof.
    assert (CSM: exists csms, Forall2 (fun imp csm => Imp2Csharpminor.compile_imp imp = OK csm) imps (nlist2list csms)).
    { depgen LINKSRC. induction COMP; ss; clarify.
      { i. des. ss. }
      unfold compile_imp, compile in H. des_ifs.
      i. destruct l.
      { unfold link_imps in LINKSRC. ss. des. clarify. exists (Coqlib.nbase p); eauto. econs; eauto. }
      des.
      assert (exists srcl2, link_imps (p0 :: l) = Some srcl2).
      { unfold link_imps in LINKSRC. ss. des_ifs. exists p1. ss. }
      apply IHCOMP in H0. des. exists (Coqlib.ncons p csms). econs; eauto. }
    des. hexploit compile_behavior_improves; eauto. i.
    des. rename tgtl into csml, H into LINKCSM, H0 into IMP2.

    assert (C2A: Coqlib.nlist_forall2 (fun csm asm => transf_csharpminor_program csm = OK asm) csms asms).
    { clear IMP2. clear LINKCSM LINKTGT. depgen asms. depgen csms. clear. induction imps; i; ss; clarify.
      { inv CSM; inv COMP. sym in H; apply n2l_not_nil in H. clarify. }
      destruct csms as [| csm csms ].
      { inv CSM. inv H4. inv COMP. inv H4. apply n2l_one in H1. clarify. econs; eauto.
        unfold compile_imp, compile in H3. des_ifs.
        unfold Imp2Csharpminor.compile_imp in H2. rewrite H2 in Heq. clarify. }
      destruct asms as [| asm asms ].
      { inv COMP. inv H4. inv CSM. inv H5. sym in H; apply n2l_not_nil in H. clarify. }
      inv CSM; inv COMP. econs; eauto.
      unfold compile_imp, compile in H3. des_ifs.
      unfold Imp2Csharpminor.compile_imp in H2. rewrite H2 in Heq. clarify. }

    move C2A after IMP2. unfold improves2_program in *.
    i.
    hexploit separate_transf_csm_program_preservation; eauto.
    i. des.
    rename beh' into beh_csm, tr_tgt into beh_asm. apply IMP2 in CSMBEH. des.
    rename tr_src into beh_imp, BEH into ASMBEH, BEH0 into IMPBEH. exists beh_imp. split; eauto.
    red. depgen SIM. depgen IMPC. clear. i.
    unfold behavior_improves in IMPC. des; clarify.

    punfold SIM. inv SIM; ss; clarify.
    unfold behavior_prefix in *. des. ss; clarify.

    depgen beh'0. depgen t. depgen beh'. induction MT; i; ss; clarify.
    { rewrite behavior_app_E0 in TB. clarify. pfold. econs 4; ss; ss.
      unfold behavior_prefix. exists (behavior_app t beh'0). rewrite behavior_app_E0. ss. }
    destruct beh'; ss; clarify.
    match goal with
    | [ |- match_beh ?_b0 _ ] => replace _b0 with (behavior_app [x] (behavior_app (l ** t0) beh'0)) end.
    2:{ rewrite <- behavior_app_assoc. ss. }
    match goal with
    | [ |- match_beh _ ?_b1 ] => replace _b1 with (Tr.app [y] (Tr.app l' Tr.ub)) end.
    2:{ rewrite <- Tr.fold_app. ss. }
    eapply match_beh_cons; eauto.
    eapply IHMT; eauto.
    instantiate (1:= Goes_wrong t0). ss.
  Qed.

  Theorem compile_behavior_improves
          (imps : list Imp.program) (asms : Coqlib.nlist Asm.program)
          (COMP: Forall2 (fun imp asm => compile_imp imp = OK asm) imps asms)
          (LINKSRC: exists impl, link_imps imps = Some impl)
    :
      exists asml, ((link_list asms = Some asml) /\
               (improves2_program (imps_sem imps) (Asm.semantics asml))).
  Proof.
    hexploit compile_behavior_improves_exists; eauto. i. des. exists asml; split; auto.
    eapply compile_behavior_improves_if_exists; eauto.
  Qed.

End PROOF.
