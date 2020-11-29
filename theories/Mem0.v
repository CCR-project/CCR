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



Section UNPADDING.
  
  Definition unpadding A {GRA} `{@GRA.inG A GRA} (a: URA.car (t:=GRA)): itree Es (URA.car (t:=A)) :=
    assume(forall n (NEQ: n <> GRA.inG_id), a n = URA.unit);;
    Ret (eq_rect_r (@URA.car) (a GRA.inG_id) GRA.inG_prf)
  .

  Definition unpadding2 {A GRA} `{@GRA.inG A GRA} (a: URA.car (t:=GRA)): itree Es (URA.car (t:=A)) :=
    n <- trigger (Choose _);;
    (if Nat.eq_dec GRA.inG_id n
     then Ret tt
     else  assume (a n = URA.unit);; Ret tt);;
    Ret (eq_rect_r (@URA.car) (a GRA.inG_id) GRA.inG_prf)
  .

End UNPADDING.
Arguments unpadding _ {GRA H}.



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

  Definition allocF (args: list val): itree Es val :=
    gr0 <- trigger (MGet "mem");;
    `m0: Mem.t <- (unpadding memRA gr0) >>= unleftU >>= unwrapU;;
    b <- trigger (Choose _);;
    guarantee(m0 b = None);;
    let m1: Mem.t := update m0 b (Some (fun _ => Vint 0)) in
    MPut "mem" (GRA.padding ((inl (Some m1)): URA.car (t:=memRA)));;
    Ret (Vptr b 0)
  .

  Definition mem: ModSem.t :=
    {|
      ModSem.sk := ["alloc" ; "store" ; "load" ; "free"];
      ModSem.sem :=
        fun _ '(Call fname args) =>
          if dec fname "alloc"
          then allocF args
          else triggerUB;
      ModSem.initial_ld := [("mem", GRA.padding (URA.black (M:=_memRA) (inr tt)))];
    |}
  .

End PROOF.
