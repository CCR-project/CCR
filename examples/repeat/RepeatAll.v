Require Import HoareDef OpenDef Open STB.
Require Import Add0 Repeat0 Add1 Repeat1 Add01proof Repeat01proof.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import ProofMode Invariant.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section PROOF.
  Let Σ: GRA.t := GRA.of_list [].
  Local Existing Instance Σ.

  Let FunStb: Sk.t -> gname -> option fspec :=
    fun sk => to_stb [("succ", succ_spec)].

  Let GlobalStb: Sk.t -> gname -> option fspec :=
    fun sk => to_closed_stb (KMod.get_stb [Add1.KAdd; Repeat1.KRepeat FunStb] sk).

  Let FunStb_incl: forall sk,
      stb_incl (FunStb sk) (GlobalStb sk).
  Proof. i. etrans; [|eapply to_closed_stb_weaker]. stb_incl_tac. Qed.

  Let GlobalStb_repeat: forall sk,
      fn_has_spec (GlobalStb sk) "repeat" (Repeat1.repeat_spec FunStb sk).
  Proof. ii. econs; ss. refl. Qed.

  Let FunStb_succ: forall sk,
      fn_has_spec (FunStb sk) "succ" (Add1.succ_spec).
  Proof. ii. econs; ss. refl. Qed.

  Let prog_tgt := [Add0.Add; Repeat0.Repeat].
  Let prog_src := KMod.transl_src_list [Add1.KAdd; Repeat1.KRepeat FunStb].

  Theorem correct: refines2 prog_tgt prog_src.
  Proof.
    etrans; cycle 1.
    { eapply adequacy_open. i. exists ε. splits; ss. g_wf_tac. }
    eapply refines2_cons.
    { eapply Add01proof.correct; et. }
    { eapply Repeat01proof.correct; et. unfold to_closed_stb. ii. des_ifs. }
  Qed.
End PROOF.
