Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Require Import SimSTS2.
Require Import Imp2Csharpminor.
Require Import Imp2CsharpminorSepComp.
Require Import Imp2Asm.
Require Import Imp2AsmProof.

Require Import Mem0 NewStackImp NewEchoImp NewEchoMainImp NewClientImp.

Set Implicit Arguments.

Section PROOF.

  Let Σ: GRA.t := GRA.of_list [].
  Local Existing Instance Σ.
  Context `{builtins : builtinsTy}.

  Definition echo_progs := [Stack_prog; Echo_prog; Client_prog; EchoMain_prog].
  
  Hypothesis source_linking: exists impl : Imp.programL, link_imps echo_progs = Some impl.

  Lemma echo_progs_improves_asm
        (asms : Coqlib.nlist Asm.program)
        (COMP: Forall2 (fun imp asm => compile_imp imp = Errors.OK asm) echo_progs asms)
    :
      exists asml, ((Linking.link_list asms = Some asml) /\
               (improves2_program (imps_sem echo_progs) (Asm.semantics asml))).
  Proof.
    hexploit compile_behavior_improves; eauto.
  Qed.

End PROOF.
