Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Set Implicit Arguments.
Set Typeclasses Depth 5.





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
        if (Z_le_gt_dec 0 sz && Z_lt_ge_dec (8 * sz) modulus_64)
        then (delta <- trigger (Choose _);;
              let m0': Mem.t := Mem.mem_pad m0 delta in
              let (blk, m1) := Mem.alloc m0' sz in
              trigger (PPut m1↑);;;
              Ret (Vptr blk 0))
        else triggerUB
    .

    Definition freeF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(b, ofs) <- (pargs [Tptr] varg)?;;
        m1 <- (Mem.free m0 b ofs)?;;
        trigger (PPut m1↑);;;
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
        trigger (PPut m1↑);;;
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



  Definition MemSem (sk: Sk.t): ModSem.t :=
    {|
      ModSem.fnsems := [("alloc", cfunU allocF) ; ("free", cfunU freeF) ; ("load", cfunU loadF) ; ("store", cfunU storeF) ; ("cmp", cfunU cmpF)];
      ModSem.mn := "Mem";
      ModSem.initial_st := (Mem.load_mem sk)↑;
    |}
  .

  Definition Mem: Mod.t := {|
    Mod.get_modsem := MemSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
