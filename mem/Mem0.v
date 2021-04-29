Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import TODOYJ.
Require Import TODO.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.
Set Typeclasses Depth 5.





(*** TODO: Move to universe.v ***)
Definition mem_pad (m0: Mem.t) (delta: nat): Mem.t :=
  Mem.mk m0.(Mem.cnts) (m0.(Mem.nb) + delta)
.

Section PROOF.
  Let memRA: URA.t := (RA.excl Mem.t).
  Context `{@GRA.inG memRA Σ}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.

  Compute (URA.car (t:=memRA)).

  Section BODY.
    Context {Es: Type -> Type}.
    Context `{has_pE: pE -< Es}.
    Context `{has_eventE: eventE -< Es}.
    Definition allocF: (list val) -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        `sz: Z <- (pargs [Tint] varg)?;;
        delta <- trigger (Choose _);;
        let m0': Mem.t := mem_pad m0 delta in
        let (blk, m1) := Mem.alloc m0' sz in
        trigger (PPut m1↑);;
        Ret (Vptr blk 0)
    .

    Definition freeF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(b, ofs) <- (pargs [Tptr] varg)?;;
        m1 <- (Mem.free m0 b ofs)?;;
        trigger (PPut m1↑);;
        Ret (Vint 0)
    .

    Definition loadF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(b, ofs) <- (pargs [Tptr] varg)?;;
        v <- (Mem.load m0 b ofs)?;;
        Ret v
    .

    Definition storeF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(b, ofs, v) <- (pargs [Tptr; Tuntyped] varg)?;;
        m1 <- (Mem.store m0 b ofs v)?;;
        trigger (PPut m1↑);;
        Ret (Vint 0)
    .

    Definition cmpF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(v0, v1) <- (pargs [Tuntyped; Tuntyped] varg)?;;
        b <- (vcmp m0 v0 v1)?;;
        if b: bool
        then Ret (Vint 1%Z)
        else Ret (Vint 0%Z)
    .

  End BODY.



  Definition MemSem: ModSem.t :=
    {|
      ModSem.fnsems := [("alloc", cfun allocF) ; ("free", cfun freeF) ; ("load", cfun loadF) ; ("store", cfun storeF) ; ("cmp", cfun cmpF)];
      ModSem.mn := "Mem";
      ModSem.initial_mr := ε;
      ModSem.initial_st := Mem.empty↑;
    |}
  .

  Definition Mem: Mod.t := {|
    Mod.get_modsem := fun _ => MemSem; (*** TODO: we need proper handling of function pointers ***)
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
