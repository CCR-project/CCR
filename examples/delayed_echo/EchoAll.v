Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import MutHeader SimModSem.
Require Import Mem1 Stack1 Echo2 EchoMain1 Client1.

Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.








Section ECHO.

  Definition Σ: GRA.t := GRA.of_list [Mem1.memRA; Echo1.echoRA].
  Local Existing Instance Σ.

  Let memRA_inG: @GRA.inG Mem1.memRA Σ.
  Proof.
    exists 0. ss.
  Qed.
  Local Existing Instance memRA_inG.

  Let echoRA_inG: @GRA.inG Echo1.echoRA Σ.
  Proof.
    exists 1. ss.
  Qed.
  Local Existing Instance echoRA_inG.

  Definition echo_spec: ModL.t :=
    Mod.add_list [
        SMod.to_src SMem;
      SMod.to_src SMain;
      SMod.to_src SStack;
      SMod.to_src SEcho;
      SMod.to_src SClient
      ].

End ECHO.

Definition echo_prog := ModSemL.initial_itr_no_check (ModL.enclose echo_spec).
