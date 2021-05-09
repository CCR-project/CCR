Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import MutHeader SimModSemL.
Require Import Mem0 Stack0 Echo0 EchoMain0 Client0 EchoAll.

Require Import TODOYJ.

Set Implicit Arguments.


Section ECHO.

  Definition Σ: GRA.t := GRA.of_list [Mem1.memRA; Auth.t (RA.excl (list Z))].
  Local Existing Instance Σ.

  Let memRA_inG: @GRA.inG Mem1.memRA Σ.
  Proof.
    exists 0. ss.
  Qed.
  Local Existing Instance memRA_inG.

  Let echoRA_inG: @GRA.inG (Auth.t (RA.excl (list Z))) Σ.
  Proof.
    exists 1. ss.
  Qed.
  Local Existing Instance echoRA_inG.

  Definition echo_impl: ModL.t :=
    Mod.add_list [
        Mem; (* Mem *)
        Main; (* Main *)
        Stack; (* Stack *)
        Echo; (* Echo *)
        Client (* Client *)
      ].

  Theorem echo_correct:
    Beh.of_program (ModL.compile echo_impl) <1= Beh.of_program (ModL.compile echo_spec).
  Proof.
    (* TODO: use Mem12proof Stack01proof Echo01proof EchoMain01proof Client01proof *)
  Admitted.

End ECHO.
