Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import MutHeader SimModSem.
Require Import Mem0 LinkedList0 Echo0 EchoMain0 Client0 EchoAll.

Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.


Section ECHO.

  Definition Σ: GRA.t := GRA.of_list [Mem1.memRA; URA.auth (RA.excl (list Z))].
  Local Existing Instance Σ.

  Let memRA_inG: @GRA.inG Mem1.memRA Σ.
  Proof.
    exists 0. ss.
  Qed.
  Local Existing Instance memRA_inG.

  Let echoRA_inG: @GRA.inG (URA.auth (RA.excl (list Z))) Σ.
  Proof.
    exists 1. ss.
  Qed.
  Local Existing Instance echoRA_inG.

  Definition echo_impl: Mod.t :=
    Mod.add_list [
        Mem ; (* Mem *)
        Main ; (* Main *)
        LinkedList ; (* LinkedList *)
        Echo ; (* Echo *)
        Client (* Client *)
      ].

  Theorem echo_correct:
    Beh.of_program (Mod.interp echo_impl) <1= Beh.of_program (Mod.interp echo_spec).
  Proof.
    (* TODO: use Mem12proof LinkedList01proof Echo01proof EchoMain01proof Client01proof *)
  Admitted.

End ECHO.
