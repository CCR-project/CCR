(** Libraries. *)
Require Import String.
From compcert Require Import
     Coqlib Errors AST Linking Smallstep Behaviors
     (** Languages (syntax and semantics). *)
     Ctypes Csyntax Csem Cstrategy Cexec
     Clight Csharpminor Cminor CminorSel RTL LTL Linear Mach Asm
     (** Translation passes. *)
     Initializers SimplExpr SimplLocals
     Cshmgen Cminorgen Selection RTLgen
     Tailcall Inlining Renumber Constprop
     CSE Deadcode Unusedglob Allocation
     Tunneling Linearize CleanupLabels Debugvar
     Stacking Asmgen
     (** Proofs of semantic preservation. *)
     SimplExprproof SimplLocalsproof Cshmgenproof
     Cminorgenproof Selectionproof RTLgenproof
     Tailcallproof Inliningproof Renumberproof
     Constpropproof CSEproof Deadcodeproof
     Unusedglobproof Allocproof Tunnelingproof
     Linearizeproof CleanupLabelsproof Debugvarproof
     Stackingproof Asmgenproof
     (** Command-line flags. *)
     Compopts
     (** Sum up *)
     Compiler Complements
.

Require Import Coqlib.
Require Import Csharpminor2Asm.

Set Implicit Arguments.


Section CSMPROOF.

  Local Open Scope string_scope.
  Local Open Scope linking_scope.

  Definition CSM's_passes :=
    mkpass Cminorgenproof.match_prog
           ::: mkpass Selectionproof.match_prog
           ::: mkpass RTLgenproof.match_prog
           ::: mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
           ::: mkpass Inliningproof.match_prog
           ::: mkpass Renumberproof.match_prog
           ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
           ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
           ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
           ::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
           ::: mkpass Unusedglobproof.match_prog
           ::: mkpass Allocproof.match_prog
           ::: mkpass Tunnelingproof.match_prog
           ::: mkpass Linearizeproof.match_prog
           ::: mkpass CleanupLabelsproof.match_prog
           ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
           ::: mkpass Stackingproof.match_prog
           ::: mkpass Asmgenproof.match_prog
           ::: pass_nil _.

  Definition match_csm_prog: Csharpminor.program -> Asm.program -> Prop :=
    pass_match (compose_passes CSM's_passes).

  Theorem transf_csm_program_match:
    forall p tp,
      transf_csharpminor_program p = Errors.OK tp ->
      match_csm_prog p tp.
  Proof.
    intros p tp T.
    unfold transf_csharpminor_program, time in T. simpl in T.
    rename p into p3.

    destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
    unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
    destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
    destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
    unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
    set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
    destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate.
    set (p9 := Renumber.transf_program p8) in *.
    set (p10 := total_if optim_constprop Constprop.transf_program p9) in *.
    set (p11 := total_if optim_constprop Renumber.transf_program p10) in *.
    destruct (partial_if optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
    destruct (partial_if optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
    destruct (Unusedglob.transform_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
    destruct (Allocation.transf_program p14) as [p15|e] eqn:P15; simpl in T; try discriminate.
    set (p16 := Tunneling.tunnel_program p15) in *.
    destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
    set (p18 := CleanupLabels.transf_program p17) in *.
    destruct (partial_if debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
    destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
    unfold match_prog; simpl.
    exists p4; split. apply Cminorgenproof.transf_program_match; auto.
    exists p5; split. apply Selectionproof.transf_program_match; auto.
    exists p6; split. apply RTLgenproof.transf_program_match; auto.
    exists p7; split. apply total_if_match. apply Tailcallproof.transf_program_match.
    exists p8; split. apply Inliningproof.transf_program_match; auto.
    exists p9; split. apply Renumberproof.transf_program_match; auto.
    exists p10; split. apply total_if_match. apply Constpropproof.transf_program_match.
    exists p11; split. apply total_if_match. apply Renumberproof.transf_program_match.
    exists p12; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
    exists p13; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
    exists p14; split. apply Unusedglobproof.transf_program_match; auto.
    exists p15; split. apply Allocproof.transf_program_match; auto.
    exists p16; split. apply Tunnelingproof.transf_program_match.
    exists p17; split. apply Linearizeproof.transf_program_match; auto.
    exists p18; split. apply CleanupLabelsproof.transf_program_match; auto.
    exists p19; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
    exists p20; split. apply Stackingproof.transf_program_match; auto.
    exists tp; split. apply Asmgenproof.transf_program_match; auto.
    reflexivity.
  Qed.

  (** CSM semantics is receptive to changes in events. *)

  Lemma csm_semantics_receptive:
    forall (p: Csharpminor.program), receptive (Csharpminor.semantics p).
  Proof.
    intros. constructor; simpl; intros.
    (* receptiveness *)
    assert (t1 = Events.E0 -> exists s2, Csharpminor.step (Globalenvs.Genv.globalenv p) s t2 s2).
    intros. subst. inv H0. exists s1; auto.
    inversion H; subst; auto.
    exploit Events.external_call_receptive; eauto. intros [vres2 [m2 EC2]].
    exists (Csharpminor.State f Csharpminor.Sskip k e (set_optvar optid vres2 le) m2). econstructor; eauto.
    exploit Events.external_call_receptive; eauto. intros [vres2 [m2 EC2]].
    exists (Csharpminor.Returnstate vres2 k m2). econstructor; eauto.
    (* trace length *)
    red; intros; inv H; simpl; try lia; eapply Events.external_call_trace_length; eauto.
  Qed.

  Theorem csm_semantic_preservation:
    forall p tp,
      match_csm_prog p tp ->
      forward_simulation (Csharpminor.semantics p) (Asm.semantics tp)
      /\ backward_simulation (Csharpminor.semantics p) (Asm.semantics tp).
  Proof.
    intros p tp M. unfold match_csm_prog, pass_match in M; simpl in M.
    Ltac DestructM :=
      match goal with
        [ H: exists p, _ /\ _ |- _ ] =>
        let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
                                                    destruct H as (p & M & MM); clear H
      end.
    repeat DestructM. subst tp.
    assert (F: forward_simulation (Csharpminor.semantics p) (Asm.semantics p18)).
    {
      eapply compose_forward_simulations.
      eapply Cminorgenproof.transl_program_correct; eassumption.
      eapply compose_forward_simulations.
      eapply Selectionproof.transf_program_correct; eassumption.
      eapply compose_forward_simulations.
      eapply RTLgenproof.transf_program_correct; eassumption.
      eapply compose_forward_simulations.
      eapply match_if_simulation. eassumption. exact Tailcallproof.transf_program_correct.
      eapply compose_forward_simulations.
      eapply Inliningproof.transf_program_correct; eassumption.
      eapply compose_forward_simulations. eapply Renumberproof.transf_program_correct; eassumption.
      eapply compose_forward_simulations.
      eapply match_if_simulation. eassumption. exact Constpropproof.transf_program_correct.
      eapply compose_forward_simulations.
      eapply match_if_simulation. eassumption. exact Renumberproof.transf_program_correct.
      eapply compose_forward_simulations.
      eapply match_if_simulation. eassumption. exact CSEproof.transf_program_correct.
      eapply compose_forward_simulations.
      eapply match_if_simulation. eassumption. exact Deadcodeproof.transf_program_correct; eassumption.
      eapply compose_forward_simulations.
      eapply Unusedglobproof.transf_program_correct; eassumption.
      eapply compose_forward_simulations.
      eapply Allocproof.transf_program_correct; eassumption.
      eapply compose_forward_simulations.
      eapply Tunnelingproof.transf_program_correct; eassumption.
      eapply compose_forward_simulations.
      eapply Linearizeproof.transf_program_correct; eassumption.
      eapply compose_forward_simulations.
      eapply CleanupLabelsproof.transf_program_correct; eassumption.
      eapply compose_forward_simulations.
      eapply match_if_simulation. eassumption. exact Debugvarproof.transf_program_correct.
      eapply compose_forward_simulations.
      eapply Stackingproof.transf_program_correct with (return_address_offset := Asmgenproof0.return_address_offset).
      exact Asmgenproof.return_address_exists.
      eassumption.
      eapply Asmgenproof.transf_program_correct; eassumption.
    }
    split. auto.
    apply forward_to_backward_simulation.
    auto.
    2:{ apply Asm.semantics_determinate. }
    apply csm_semantics_receptive.
  Qed.



  Lemma separate_transf_csm_program_correct :
    forall (c_units : Coqlib.nlist Csharpminor.program) (asm_units : Coqlib.nlist Asm.program) (c_program : Csharpminor.program)
      (COMPS: Coqlib.nlist_forall2 (fun cu tcu => transf_csharpminor_program cu = Errors.OK tcu) c_units asm_units)
      (LINKCSM: link_list c_units = Some c_program),
    exists asm_program : Asm.program,
      (link_list asm_units = Some asm_program) /\ (backward_simulation (Csharpminor.semantics c_program) (Asm.semantics asm_program)).
  Proof.
    intros.
    assert (nlist_forall2 match_csm_prog c_units asm_units).
    { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_csm_program_match; auto. }
    assert (exists asm_program, link_list asm_units = Some asm_program /\ match_csm_prog c_program asm_program).
    { eapply link_list_compose_passes; eauto. }
    destruct H0 as (asm_program & P & Q).
    exists asm_program; split; auto.
    apply csm_semantic_preservation; auto.
  Qed.

  Lemma separate_transf_csm_program_preservation
        (csms: Coqlib.nlist Csharpminor.program) csml
        (asms: Coqlib.nlist Asm.program) asml
        beh
        (COMP: Coqlib.nlist_forall2 (fun csm asm => transf_csharpminor_program csm = Errors.OK asm) csms asms)
        (CSMLINK: link_list csms = Some csml)
        (ASMLINK: link_list asms = Some asml)
        (ASMBEH: program_behaves (Asm.semantics asml) beh)
    :
      exists beh', ((<<CSMBEH: program_behaves (Csharpminor.semantics csml) beh'>>) /\
               (<<IMPC: behavior_improves beh' beh>>)).
  Proof.
    intros. exploit separate_transf_csm_program_correct; eauto. intros (a & P & Q).
    assert (a = asml) by congruence. subst a. 
    eapply backward_simulation_behavior_improves; eauto.
  Qed.

End CSMPROOF.
