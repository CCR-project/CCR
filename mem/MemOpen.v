Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic.
Require Import TODO.
Require Import Mem0 Mem1.
Require Import OpenDef Open.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.





Let _memRA: URA.t := (block ==> Z ==> (Excl.t val))%ra.

Section PROOF.
  Context `{@GRA.inG memRA Σ}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("malloc", mk_specbody alloc_spec allocF);
    ("free",   mk_specbody free_spec freeF);
    ("load",   mk_specbody load_spec loadF);
    ("store",  mk_specbody store_spec storeF);
    ("cmp",    mk_specbody cmp_spec cmpF)
    ]
  .

  Definition KMemSem (sk: Sk.t): KModSem.t := {|
    KModSem.fnsems := MemSbtb;
    KModSem.mn := "Mem";
    KModSem.initial_mr := (GRA.embed (Auth.black (M:=_memRA) ε));
    KModSem.initial_st := (Sk.load_mem sk)↑;
  |}
  .

  Definition SMemSem: Sk.t -> SModSem.t := (disclose_smodsem ∘ KModSem.to_tgt) ∘ KMemSem.

  Definition MemSem: Sk.t -> ModSem.t := (SModSem.to_tgt []) ∘ SMemSem.

  Definition KMem: KMod.t := {|
    KMod.get_modsem := KMemSem;
    KMod.sk := Sk.unit;
  |}
  .

  Definition SMem: SMod.t := KMod.to_tgt KMem.

  Definition Mem: Mod.t := SMod.to_tgt (fun _ => []) SMem.

End PROOF.
Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
