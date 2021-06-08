Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import SimModSem.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import Logic OpenDef.

Set Implicit Arguments.

Section PROOF.

  Context `{Σ: GRA.t}.

  Definition DebugStb: list (gname * fspec).
   eapply (Seal.sealing "stb").
   eapply [("debug", (mk_simple (X:=unit) (fun _ => ((fun _ o => (⌜o = ord_top⌝: iProp)%I),
                                                     (fun _ => (⌜True⌝: iProp)%I)))))].
  Defined.

End PROOF.

Global Hint Unfold DebugStb: stb.
