Require Import Coqlib ITreelib ImpPrelude STS Behavior.
Require Import ModSem Skeleton PCM STB OpenDef.
Require Import Open.
Require Import Mem0 Mem1 Stack3A.
Require Import Imp StackImp EchoImp EchoMainImp ClientImp.

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
Require Import Mem0 StackImp EchoImp EchoMainImp ClientImp.
Section ECHOIMP.
  Definition echo_progs := [Stack_prog; Echo_prog; EchoMain_prog; Client_prog].
  Definition echo_imp: ModL.t :=
    Mod.add_list (Mem (fun _ => false) :: map ImpMod.get_mod echo_progs).

  Definition echo_imp_itr := ModSemL.initial_itr (ModL.enclose echo_imp) None.
End ECHOIMP.


Require Import Mem0 Stack0 Echo0 EchoMain0 Client0.
Section ECHOIMPL.
  Definition echo_impl: ModL.t :=
    Mod.add_list [Mem (fun _ => false); Stack; Echo; Main; Client].

  Definition echo_impl_itr := ModSemL.initial_itr (ModL.enclose echo_impl) None.
End ECHOIMPL.


Require Import MemOpen Stack3A Echo1 EchoMain0 Client0.
(* spec program *)
Require Import Stack2.
Section ECHOSPEC.
  Definition echo_spec: ModL.t :=
    Mod.add_list [
        Mem0.Mem (fun _ => true);
      Stack2.Stack;
      KMod.transl_src (fun _ => ["Echo"]) KEcho;
      Main; Client
      ].

  Definition echo_spec_itr := ModSemL.initial_itr (ModL.enclose echo_spec) None.
End ECHOSPEC.



Require Import Mem0Openproof MemOpen0proof.
Require Import StackImp0proof Stack01proof Stack12proof Stack23Aproof.
Require Import EchoMainImp0proof EchoImp0proof.
Require Import ClientImp0proof Echo01proof.
Require Import Echo1mon Stack32proof.
Section PROOF.
  Theorem echo_correct:
    refines2 [Mem0.Mem (fun _ => false); StackImp.Stack; EchoImp.Echo]
             [Mem0.Mem (fun _ => true); Stack2.Stack; KMod.transl_src (fun _ => ["Echo"]) KEcho].
  Proof.
    transitivity (KMod.transl_tgt_list [KMem (fun _ => true) (fun _ => true); Stack1.KStack]++[EchoImp.Echo]).
    { eapply refines2_cons.
      { eapply Mem0Openproof.correct. i; ss. }
      eapply refines2_cons; [|refl].
      { etrans.
        { eapply StackImp0proof.correct. }
        { eapply Stack01proof.correct. i.
          etrans; [|eapply to_closed_stb_weaker]. stb_incl_tac; tauto. }
      }
    }
    etrans.
    { eapply refines2_app; [|refl].
      eapply adequacy_open. i. exists ε. split.
      { g_wf_tac. repeat (i; splits; ur; ss).
        { r. esplits; et. rewrite URA.unit_idl. refl. }
        { unfold initial_mem_mr. des_ifs; ss. }
      }
      { ii. ss. }
    }
    eapply refines2_cons.
    { eapply MemOpen0proof.correct. }
    transitivity (KMod.transl_tgt_list [Stack3A.KStack; KEcho]).
    { eapply refines2_cons.
      { etrans.
        { eapply Stack12proof.correct. }
        { eapply Stack23Aproof.correct. }
      }
      { etrans.
        { eapply EchoImp0proof.correct. }
        { eapply Echo01proof.correct.
          stb_context_incl_tac; tauto. }
      }
    }
    etrans.
    { eapply adequacy_open. i. exists ε. split.
      { g_wf_tac; repeat (i; splits; ur; ss). refl. }
      { ii. ss. }
    }
    { eapply refines2_cons.
      { eapply Stack32proof.correct. }
      eapply refines2_cons; [|refl].
      { eapply Echo1mon.correct. ii. ss. des; auto. }
    }
  Qed.

  Corollary echo_closed_correct:
    refines_closed echo_imp echo_spec.
  Proof.
    eapply refines_close. hexploit refines2_app.
    { eapply echo_correct. }
    { eapply refines2_cons.
      { eapply EchoMainImp0proof.correct. }
      { eapply ClientImp0proof.correct. }
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
