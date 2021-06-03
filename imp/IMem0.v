Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
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

  Definition allocF_parg (args: list val): option Z :=
    match args with
    | [Vint sz] => Some sz
    | _ => None
    end
  .

  Definition allocF: list val -> itree Es val :=
    fun varg =>
      mp0 <- trigger (PGet);;
      m0 <- mp0↓?;;
      `sz: Z <- (allocF_parg varg)?;;
      let (blk, m1) := Mem.alloc m0 sz in
      trigger (PPut m1↑);;;
      Ret (Vptr blk 0)
  .

  Definition freeF_parg (args: list val): option (mblock * Z) :=
    match args with
    | [Vptr b ofs] => Some (b, ofs)
    | _ => None
    end
  .

  Definition freeF: list val -> itree Es val :=
    fun varg =>
      mp0 <- trigger (PGet);;
      m0 <- mp0↓?;;
      '(b, ofs) <- (freeF_parg varg)?;;
      m1 <- (Mem.free m0 b ofs)?;;
      trigger (PPut m1↑);;;
      Ret (Vint 0)
  .

  Definition loadF_parg (args: list val): option (mblock * Z) :=
    match args with
    | [Vptr b ofs] => Some (b, ofs)
    | _ => None
    end
  .

  Definition loadF: list val -> itree Es val :=
    fun varg =>
      mp0 <- trigger (PGet);;
      m0 <- mp0↓?;;
      '(b, ofs) <- (loadF_parg varg)?;;
      v <- (Mem.load m0 b ofs)?;;
      Ret v
  .

  Definition storeF_parg (args: list val): option (mblock * Z * val) :=
    match args with
    | [Vptr b ofs; v] => Some (b, ofs, v)
    | _ => None
    end
  .

  Definition storeF: list val -> itree Es val :=
    fun varg =>
      mp0 <- trigger (PGet);;
      m0 <- mp0↓?;;
      '(b, ofs, v) <- (storeF_parg varg)?;;
      m1 <- (Mem.store m0 b ofs v)?;;
      trigger (PPut m1↑);;;
      Ret (Vint 0)
  .

  Definition cmpF_parg (args: list val): option (val * val) :=
    match args with
    | [v0; v1] => Some (v0, v1)
    | _ => None
    end
  .

  Definition cmpF: list val -> itree Es val :=
    fun varg =>
      mp0 <- trigger (PGet);;
      m0 <- mp0↓?;;
      '(v0, v1) <- (cmpF_parg varg)?;;
      b <- (vcmp m0 v0 v1)?;;
      if b: bool
      then Ret (Vint 1%Z)
      else Ret (Vint 0%Z)
  .

  Definition IMemSem (sk: Sk.t): ModSem.t :=
    {|
      ModSem.fnsems := [("alloc", cfun allocF) ; ("free", cfun freeF) ; ("load", cfun loadF) ; ("store", cfun storeF) ; ("cmp", cfun cmpF)];
      ModSem.mn := "Mem";
      ModSem.initial_mr := ε;
      ModSem.initial_st := (Sk.load_mem sk)↑;
    |}
  .

  Definition IMem: Mod.t := {|
    Mod.get_modsem := IMemSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
