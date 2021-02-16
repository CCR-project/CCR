Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.
Set Typeclasses Depth 4.



Definition unleftU {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
  match xy with
  | inl x => Ret x
  | inr y => triggerUB
  end.

Definition unleftN {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
  match xy with
  | inl x => Ret x
  | inr y => triggerNB
  end.

Definition unrightU {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
  match xy with
  | inl x => triggerUB
  | inr y => Ret y
  end.

Definition unrightN {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
  match xy with
  | inl x => triggerNB
  | inr y => Ret y
  end.

Section UNPADDING.
  
  Definition unpadding A {Σ} `{@GRA.inG A Σ} (a: URA.car (t:=Σ)): itree Es (URA.car (t:=A)) :=
    assume(forall n (NEQ: n <> GRA.inG_id), a n = URA.unit);;
    Ret (eq_rect_r (@URA.car) (a GRA.inG_id) GRA.inG_prf)
  .

  Definition unpadding2 {A Σ} `{@GRA.inG A Σ} (a: URA.car (t:=Σ)): itree Es (URA.car (t:=A)) :=
    n <- trigger (Choose _);;
    (if Nat.eq_dec GRA.inG_id n
     then Ret tt
     else  assume (a n = URA.unit);; Ret tt);;
    Ret (eq_rect_r (@URA.car) (a GRA.inG_id) GRA.inG_prf)
  .

End UNPADDING.
Arguments unpadding _ {Σ H}.





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

  Definition allocF (varg: Any.t): itree Es Any.t :=
    varg <- varg↓ǃ;;
    mr0 <- trigger (MGet "Mem");;
    (* `m0: Mem.t <- (unpadding memRA mr0) >>= unleftU >>= unwrapU;; *)
    `m0: Mem.t <- trigger (Take _);;
    assume(mr0 = GRA.padding ((inl (Some m0)): URA.car (t:=memRA)));;
    `sz: Z <- (allocF_parg varg)?;;
    let (blk, m1) := Mem.alloc m0 sz in
    trigger (MPut "Mem" (GRA.padding ((inl (Some m1)): URA.car (t:=memRA))));;
    Ret (Vptr blk 0)↑
  .

  Definition freeF_parg (args: list val): option (block * Z) :=
    match args with
    | [Vptr b ofs] => Some (b, ofs)
    | _ => None
    end
  .

  Definition freeF (varg: Any.t): itree Es Any.t :=
    varg <- varg↓ǃ;;
    mr0 <- trigger (MGet "Mem");;
    (* `m0: Mem.t <- (unpadding memRA mr0) >>= unleftU >>= unwrapU;; *)
    `m0: Mem.t <- trigger (Take _);;
    assume(mr0 = GRA.padding ((inl (Some m0)): URA.car (t:=memRA)));;
    '(b, ofs) <- (freeF_parg varg)?;;
    m1 <- (Mem.free m0 b ofs)?;;
    trigger (MPut "Mem" (GRA.padding ((inl (Some m1)): URA.car (t:=memRA))));;
    Ret (Vint 0)↑
  .

  Definition loadF_parg (args: list val): option (block * Z) :=
    match args with
    | [Vptr b ofs] => Some (b, ofs)
    | _ => None
    end
  .

  Definition loadF (varg: Any.t): itree Es Any.t :=
    varg <- varg↓ǃ;;
    mr0 <- trigger (MGet "Mem");;
    (* `m0: Mem.t <- (unpadding memRA mr0) >>= unleftU >>= unwrapU;; *)
    `m0: Mem.t <- trigger (Take _);;
    assume(mr0 = GRA.padding ((inl (Some m0)): URA.car (t:=memRA)));;
    '(b, ofs) <- (loadF_parg varg)?;;
    v <- (Mem.load m0 b ofs)?;;
    Ret v↑
  .

  Definition storeF_parg (args: list val): option (block * Z * val) :=
    match args with
    | [Vptr b ofs; v] => Some (b, ofs, v)
    | _ => None
    end
  .

  Definition storeF (varg: Any.t): itree Es Any.t :=
    varg <- varg↓ǃ;;
    mr0 <- trigger (MGet "Mem");;
    (* `m0: Mem.t <- (unpadding memRA mr0) >>= unleftU >>= unwrapU;; *)
    `m0: Mem.t <- trigger (Take _);;
    assume(mr0 = GRA.padding ((inl (Some m0)): URA.car (t:=memRA)));;
    '(b, ofs, v) <- (storeF_parg varg)?;;
    m1 <- (Mem.store m0 b ofs v)?;;
    trigger (MPut "Mem" (GRA.padding ((inl (Some m1)): URA.car (t:=memRA))));;
    Ret (Vint 0)↑
  .

  Definition MemSem: ModSem.t :=
    {|
      ModSem.fnsems := [("alloc", allocF) ; ("free", freeF) ; ("load", loadF) ; ("store", storeF)];
      ModSem.initial_mrs := [("Mem", GRA.padding ((inl (Some Mem.empty)): URA.car (t:=memRA)))];
    |}
  .

  Definition Mem: Mod.t := {|
    Mod.get_modsem := fun _ => MemSem; (*** TODO: we need proper handling of function pointers ***)
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
