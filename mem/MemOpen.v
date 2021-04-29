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





Definition mem_pad (m0: Mem.t) (delta: nat): Mem.t :=
  Mem.mk m0.(Mem.cnts) (m0.(Mem.nb) + delta)
.

Let _memRA: URA.t := (block ==> Z ==> (Excl.t val))%ra.

Section PROOF.
  Context `{@GRA.inG memRA Σ}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.



  (* Definition alloc_body: (list val) -> itree (hCallE +' pE +' eventE) val := *)
  (*   fun varg => *)
  (*     mp0 <- trigger (PGet);; *)
  (*     m0 <- mp0↓?;; *)
  (*     `sz: Z <- (pargs [Tint] varg)?;; *)
  (*     delta <- trigger (Choose _);; *)
  (*     let m0': Mem.t := mem_pad m0 delta in *)
  (*     let (blk, m1) := Mem.alloc m0' sz in *)
  (*     trigger (PPut m1↑);; *)
  (*     Ret (Vptr blk 0) *)
  (* . *)

  (* Definition free_body: (list val) -> itree (hCallE +' pE +' eventE) val := *)
  (*   fun varg => *)
  (*     mp0 <- trigger (PGet);; *)
  (*     m0 <- mp0↓?;; *)
  (*     '(b, ofs) <- (pargs [Tptr] varg)?;; *)
  (*     m1 <- (Mem.free m0 b ofs)?;; *)
  (*     trigger (PPut m1↑);; *)
  (*     Ret (Vint 0) *)
  (* . *)

  Definition MemSbtb: list (gname * fspecbody) :=
    [("alloc", mk_specbody alloc_spec allocF);
    ("free",   mk_specbody free_spec freeF);
    ("load",   mk_specbody load_spec loadF);
    ("store",  mk_specbody store_spec storeF);
    ("cmp",    mk_specbody cmp_spec cmpF)
    ]
  .

  Definition _SMemSem: SModSem.t := {|
    SModSem.fnsems := MemSbtb;
    SModSem.mn := "Mem";
    SModSem.initial_mr := (GRA.embed (Auth.black (M:=_memRA) ε));
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SMemSem: SModSem.t := disclose_smodsem _SMemSem.

  Definition MemSem: ModSem.t := (SModSem.to_tgt MemStb) SMemSem.

  Definition _SMem: SMod.t := {|
    SMod.get_modsem := fun _ => _SMemSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition SMem: SMod.t := disclose_smod _SMem.

End PROOF.
Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
