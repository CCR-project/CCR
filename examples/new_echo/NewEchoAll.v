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
Require Import Mem0 NewStack0 NewEcho0 NewEchoMain0 NewClient0.


Set Implicit Arguments.




Section ECHOIMPL.

  Let Σ: GRA.t := GRA.of_list [].
  Local Existing Instance Σ.

  Definition echo_impl: ModL.t :=
    Mod.add_list [Mem; Stack; Echo; Main; Client].

End ECHOIMPL.

Definition echo_impl_itr := ModSemL.initial_itr (ModL.enclose echo_impl) None.




Require Import Mem0 NewStackImp NewEchoImp NewEchoMainImp NewClientImp.

Section ECHOIMP.

  Let Σ: GRA.t := GRA.of_list [].
  Local Existing Instance Σ.

  Definition echo_imp: ModL.t :=
    Mod.add_list [Mem; Stack; Echo; EchoMain; Client].

End ECHOIMP.

Definition echo_imp_itr := ModSemL.initial_itr (ModL.enclose echo_imp) None.



Require Import MemOpen NewStack3A NewEcho1 NewEchoMain0 NewClient0.
Require Import NewEchoMainImp0proof NewStackImp0proof NewEchoImp0proof NewClientImp0proof NewStack01proof NewStack12proof NewStack23Aproof NewEcho01proof.
Require Import SimModSem.
Require Import Mem0Openproof MemOpen0proof.
Require Import Open.

Section ECHOSPEC.

  Let Σ: GRA.t := GRA.of_list [Mem1.memRA; stkRA].
  Local Existing Instance Σ.

  Let memRA_inG: @GRA.inG Mem1.memRA Σ.
  Proof.
    exists 0. ss.
  Qed.
  Local Existing Instance memRA_inG.

  Let stkRA_inG: @GRA.inG stkRA Σ.
  Proof.
    exists 1. ss.
  Qed.
  Local Existing Instance stkRA_inG.

  Let frds: list string := ["Stack"; "Echo"].
  Definition echo_spec: ModL.t :=
    Mod.add_list [
      Mem0.Mem;
      (KMod.transl_src (fun _ => frds) KStack);
      (KMod.transl_src (fun _ => frds) KEcho);
      Main;
      Client
      ].

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
        eapply adequacy_open. }
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
        { eapply adequacy_local2. eapply NewEcho01proof.correct. i.
          autounfold with stb. admit "stb". }
        refl.
      }
      eapply refines2_cons; [refl|].
      transitivity (KMod.transl_src_list kmd1 ++ [Main; Client]); [|refl].
      eapply refines2_app; [|refl].
      eapply adequacy_open.
    Qed.
  End PROOF.
End ECHOSPEC.

Definition echo_spec_itr := ModSemL.initial_itr (ModL.enclose echo_spec) None.
