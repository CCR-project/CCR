Require Import Coqlib ITreelib ImpPrelude STS Behavior.
Require Import ModSem Skeleton PCM STB OpenDef.
Require Import Open.
Require Import Mem0 Mem1 NewStack3A.
Require Import Imp NewStackImp NewEchoImp NewEchoMainImp NewClientImp.

Set Implicit Arguments.



Definition EchoGRA: GRA.t := GRA.of_list [Mem1.memRA; stkRA].
Local Existing Instance EchoGRA.

Instance memRA_inG: @GRA.inG Mem1.memRA EchoGRA.
Proof.
  exists 0. ss. Show Proof.
Defined.
Local Existing Instance memRA_inG.

Instance stkRA_inG: @GRA.inG stkRA EchoGRA.
Proof.
  exists 1. ss.
Defined.
Local Existing Instance stkRA_inG.



(* Imp program *)
Require Import Mem0 NewStackImp NewEchoImp NewEchoMainImp NewClientImp.
Section ECHOIMP.
  Definition echo_progs := [Stack_prog; Echo_prog; EchoMain_prog; Client_prog].
  Definition echo_imp: ModL.t :=
    Mod.add_list (Mem :: map ImpMod.get_mod echo_progs).

  Definition echo_imp_itr := ModSemL.initial_itr (ModL.enclose echo_imp) None.
End ECHOIMP.


Require Import Mem0 NewStack0 NewEcho0 NewEchoMain0 NewClient0.
Section ECHOIMPL.
  Definition echo_impl: ModL.t :=
    Mod.add_list [Mem; Stack; Echo; Main; Client].

  Definition echo_impl_itr := ModSemL.initial_itr (ModL.enclose echo_impl) None.
End ECHOIMPL.


Require Import MemOpen NewStack3A NewEcho1 NewEchoMain0 NewClient0.
(* spec program *)
Require Import NewStack2.
Section ECHOSPEC.
  Definition echo_spec: ModL.t :=
    Mod.add_list [
        Mem0.Mem;
      NewStack2.Stack;
      KMod.transl_src (fun _ => ["Echo"]) KEcho;
      Main; Client
      ].

  Definition echo_spec_itr := ModSemL.initial_itr (ModL.enclose echo_spec) None.
End ECHOSPEC.



Require Import Mem0Openproof MemOpen0proof.
Require Import NewStackImp0proof NewStack01proof NewStack12proof NewStack23Aproof.
Require Import NewEchoMainImp0proof NewEchoImp0proof.
Require Import NewClientImp0proof NewEcho01proof.
Require Import NewEcho1mon NewStack32proof.
Section PROOF.
  Theorem echo_correct:
    refines2 [Mem0.Mem; NewStackImp.Stack; NewEchoImp.Echo]
             [Mem0.Mem; NewStack2.Stack; KMod.transl_src (fun _ => ["Echo"]) KEcho].
  Proof.
    transitivity (KMod.transl_tgt_list [KMem; NewStack1.KStack]++[NewEchoImp.Echo]).
    { eapply refines2_cons.
      { eapply Mem0Openproof.correct. }
      eapply refines2_cons; [|refl].
      { etrans.
        { eapply NewStackImp0proof.correct. }
        { eapply NewStack01proof.correct. i.
          etrans; [|eapply to_closed_stb_weaker]. stb_incl_tac; tauto. }
      }
    }
    etrans.
    { eapply refines2_app; [|refl].
      eapply adequacy_open. i. exists ε. split.
      { g_wf_tac. repeat (i; splits; ur; ss). refl. }
      { ii. ss. }
    }
    eapply refines2_cons.
    { eapply MemOpen0proof.correct. }
    transitivity (KMod.transl_tgt_list [NewStack3A.KStack; KEcho]).
    { eapply refines2_cons.
      { etrans.
        { eapply NewStack12proof.correct. }
        { eapply NewStack23Aproof.correct. }
      }
      { etrans.
        { eapply NewEchoImp0proof.correct. }
        { eapply NewEcho01proof.correct.
          stb_context_incl_tac; tauto. }
      }
    }
    etrans.
    { eapply adequacy_open. i. exists ε. split.
      { g_wf_tac; repeat (i; splits; ur; ss). refl. }
      { ii. ss. }
    }
    { eapply refines2_cons.
      { eapply NewStack32proof.correct. }
      eapply refines2_cons; [|refl].
      { eapply NewEcho1mon.correct. ii. ss. des; auto. }
    }
  Qed.

  Corollary echo_closed_correct:
    refines_closed echo_imp echo_spec.
  Proof.
    eapply refines_close. hexploit refines2_app.
    { eapply echo_correct. }
    { eapply refines2_cons.
      { eapply NewEchoMainImp0proof.correct. }
      { eapply NewClientImp0proof.correct. }
    }
    ss.
  Qed.
End PROOF.


Require Import SimSTS2 Imp2Csharpminor Imp2Asm.
Require Import Imp2AsmProof.
Section PROOF.
  Context `{builtins : builtinsTy}.
  Hypothesis source_linking: exists impl, link_imps echo_progs = Some impl.

  Theorem echo_compile_correct
          (asms : Coqlib.nlist Asm.program)
          (COMP: Forall2 (fun imp asm => compile_imp imp = Errors.OK asm) echo_progs asms)
    :
      exists asml, (Linking.link_list asms = Some asml) /\
                   (improves2_program (ModL.compile echo_spec) (Asm.semantics asml)).
  Proof.
    hexploit compile_behavior_improves; [et|et|]. i. des. esplits; [et|].
    eapply improves_combine; [|et]. eapply echo_closed_correct.
  Qed.
End PROOF.
