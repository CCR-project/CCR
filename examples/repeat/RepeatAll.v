Require Import HoareDef STB Add1 Repeat1 SimModSem.
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

Section EQUATION.
  Context `{Σ: GRA.t}.

  Let FunStb: Sk.t -> gname -> option fspec :=
    fun sk => to_stb [("succ", succ_spec)].

  Let GlobalStb: Sk.t -> gname -> option fspec :=
    fun sk => to_stb (SMod.get_stb [Add1.SAdd; Repeat1.SRepeat FunStb] sk).

  Let FunStb_incl: forall sk,
      stb_incl (FunStb sk) (GlobalStb sk).
  Proof. stb_incl_tac. Qed.

  Let GlobalStb_repeat: forall sk,
      fn_has_spec (GlobalStb sk) "repeat" (Repeat1.repeat_spec FunStb sk).
  Proof. ii. econs; ss. refl. Qed.

  Let FunStb_succ: forall sk,
      fn_has_spec (FunStb sk) "succ" (Add1.succ_spec).
  Proof. ii. econs; ss. refl. Qed.
End EQUATION.
