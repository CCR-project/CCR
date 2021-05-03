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
Require Import Open.

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

  Definition _SMemSem (sk: Sk.t): SModSem.t := {|
    SModSem.fnsems := MemSbtb;
    SModSem.mn := "Mem";
    SModSem.initial_mr := (GRA.embed (Auth.black (M:=_memRA) ε));
    SModSem.initial_st := (Sk.load_mem sk)↑;
  |}
  .

  Definition SMemSem: Sk.t -> SModSem.t := disclose_smodsem ∘ _SMemSem.

  Definition MemSem: Sk.t -> ModSem.t := (SModSem.to_tgt MemStb) ∘ SMemSem.

  Definition _SMem: SMod.t := {|
    SMod.get_modsem := _SMemSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition SMem: SMod.t := disclose_smod _SMem.

End PROOF.
Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
