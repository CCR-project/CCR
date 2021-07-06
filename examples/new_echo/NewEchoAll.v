Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import MutHeader SimModSem.
Require Import OpenDef.
Require Import Mem0 NewStack3A NewStack0 NewEcho0 NewEchoMain0 NewClient0.

Set Implicit Arguments.


Definition EchoGRA: GRA.t := GRA.of_list [Mem1.memRA; stkRA].
Local Existing Instance EchoGRA.

Instance memRA_inG: @GRA.inG Mem1.memRA EchoGRA.
Proof.
  exists 0. ss.
Qed.
Local Existing Instance memRA_inG.

Instance stkRA_inG: @GRA.inG stkRA EchoGRA.
Proof.
  exists 1. ss.
Qed.
Local Existing Instance stkRA_inG.



Section ECHOIMPL.
  Definition echo_impl: ModL.t :=
    Mod.add_list [Mem; Stack; Echo; Main; Client].
  Definition echo_impl_itr := ModSemL.initial_itr (ModL.enclose echo_impl) None.
End ECHOIMPL.


Require Import Mem0 NewStackImp NewEchoImp NewEchoMainImp NewClientImp.
Section ECHOIMP.
  Definition echo_imp: ModL.t :=
    Mod.add_list [Mem; Stack; Echo; EchoMain; Client].
  Definition echo_imp_itr := ModSemL.initial_itr (ModL.enclose echo_imp) None.
End ECHOIMP.


Require Import MemOpen NewStack3A NewEcho1 NewEchoMain0 NewClient0.
Section ECHOSPEC.
  Let frds: list string := ["Stack"; "Echo"].
  Definition echo_spec: ModL.t :=
    Mod.add_list [
      Mem0.Mem;
      (KMod.transl_src (fun _ => frds) KStack);
      (KMod.transl_src (fun _ => frds) KEcho);
      Main;
      Client
      ].

  Definition echo_spec_itr := ModSemL.initial_itr (ModL.enclose echo_spec) None.
End ECHOSPEC.


Lemma refines2_cons mhd0 mhd1 mtl0 mtl1
      (HD: refines2 [mhd0] [mhd1])
      (TL: refines2 mtl0 mtl1)
  :
    refines2 (mhd0::mtl0) (mhd1::mtl1).
Proof.
Admitted.

Lemma refines2_app mhd0 mhd1 mtl0 mtl1
      (HD: refines2 mhd0 mhd1)
      (TL: refines2 mtl0 mtl1)
  :
    refines2 (mhd0++mtl0) (mhd1++mtl1).
Proof.
Admitted.

Require Import NewEchoMainImp0proof NewStackImp0proof NewEchoImp0proof NewClientImp0proof NewStack01proof NewStack12proof NewStack23Aproof NewEcho01proof.
Require Import SimModSem.
Require Import Mem0Openproof MemOpen0proof.
Require Import Open.


Section PROOF.
  Theorem echo_correct:
    refines echo_imp echo_spec.
  Proof.
    unfold echo_imp, echo_spec. transitivity echo_impl.
    { eapply refines2_pairwise. econs.
      { ss. }
      econs.
      { eapply adequacy_local2. eapply NewStackImp0proof.correct. }
      econs.
      { eapply adequacy_local2. eapply NewEchoImp0proof.correct. }
      econs.
      { eapply adequacy_local2. eapply NewEchoMainImp0proof.correct. }
      econs.
      { eapply adequacy_local2. eapply NewClientImp0proof.correct. }
      ss.
    }
    unfold echo_impl.
    pose (kmd0 := [KMem; NewStack1.KStack]).
    transitivity (Mod.add_list (KMod.transl_tgt_list kmd0 ++ [NewEcho0.Echo; NewEchoMain0.Main; Client])).
    { eapply refines2_cons.
      { eapply adequacy_local2. eapply Mem0Openproof.correct. }
      eapply refines2_cons.
      { eapply adequacy_local2. eapply NewStack01proof.correct. i.
        etrans; [|eapply to_closed_stb_weaker].
        stb_incl_tac; tauto. }
      refl.
    }
    etrans.
    { rewrite Mod.add_list_app. eapply refines_proper_r.
      eapply adequacy_open. i. exists ε. split.
      { admit "URA wf". }
      { ii. ss. }
    }
    pose (kmd1 := [NewStack3A.KStack; KEcho]).
    transitivity (Mod.add_list (Mem0.Mem :: (KMod.transl_tgt_list kmd1) ++ [Main; Client])).
    { rewrite <- Mod.add_list_app. eapply refines2_cons.
      { eapply adequacy_local2. eapply MemOpen0proof.correct. }
      eapply refines2_cons.
      { etrans.
        { eapply adequacy_local2. eapply NewStack12proof.correct. }
        { eapply adequacy_local2. eapply NewStack23Aproof.correct. }
      }
      eapply refines2_cons.
      { eapply adequacy_local2. eapply NewEcho01proof.correct.
        stb_context_incl_tac; tauto. }
      refl.
    }
    eapply refines2_cons; [refl|].
    transitivity (KMod.transl_src_list kmd1 ++ [Main; Client]); [|refl].
    eapply refines2_app; [|refl].
    eapply adequacy_open. i. exists ε. split.
    { admit "URA wf". }
    { ii. ss. }
  Qed.
End PROOF.
