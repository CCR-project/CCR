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
Require Import OpenDef.
(* Require Import Mem1 Stack1 Echo2 EchoMain1 Client1. *)
Require Import Mem0 NewStack0 NewEcho0 NewEchoMain0 NewClient0.

Require Import TODOYJ.

Set Implicit Arguments.







Section ECHOIMPL.

  Definition Σ: GRA.t := GRA.of_list [].
  Local Existing Instance Σ.

  Definition echo_impl: ModL.t :=
    Mod.add_list [Mem; Main; Stack; Echo; (UMod.transl Client)].

End ECHOIMPL.

Definition echo_impl_itr := ModSemL.initial_itr (ModL.enclose echo_impl) None.

(* Section ECHOSPEC. *)

(*   Definition Σ: GRA.t := GRA.of_list [Mem1.memRA; Echo1.echoRA]. *)
(*   Local Existing Instance Σ. *)

(*   Let memRA_inG: @GRA.inG Mem1.memRA Σ. *)
(*   Proof. *)
(*     exists 0. ss. *)
(*   Qed. *)
(*   Local Existing Instance memRA_inG. *)

(*   Let echoRA_inG: @GRA.inG Echo1.echoRA Σ. *)
(*   Proof. *)
(*     exists 1. ss. *)
(*   Qed. *)
(*   Local Existing Instance echoRA_inG. *)

(*   Definition echo_spec: ModL.t := *)
(*     Mod.add_list [ *)
(*         SMod.to_src SMem; *)
(*       SMod.to_src SMain; *)
(*       SMod.to_src SStack; *)
(*       SMod.to_src SEcho; *)
(*       SMod.to_src SClient *)
(*       ]. *)

(* End ECHOSPEC. *)

(* Definition echo_prog := ModSemL.initial_itr (ModL.enclose echo_spec) None. *)
