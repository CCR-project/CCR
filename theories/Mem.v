Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.









Let _memRA: URA.t := (RA.pointwise block (RA.pointwise Z (RA.excl val))).
Instance memRA: URA.t := URA.auth _memRA.
Compute (URA.car).

Definition points_to (loc: block * Z) (v: val): URA.car :=
  let (b, ofs) := loc in
  URA.white (M:=_memRA)
            (inl (fun _b _ofs => if (dec _b b) && (dec _ofs ofs) then Some v else None)).

Definition own {GRA: GRA.t} (whole a: URA.car (t:=GRA)): Prop := URA.extends a whole.

Notation "loc |-> v" := (points_to loc v) (at level 20).




Section PROOF.
  Context `{@GRA.inG memRA Σ}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.

  Definition allocF_parg (args: list val): option Z :=
    match args with
    | [Vint sz] => Some sz
    | _ => None
    end
  .

  Definition allocF (args: list val): itree Es val :=
    sz <- (allocF_parg args)?;;
    r <- trigger (Take URA.car);;
    assume(URA.extends URA.unit r);;
    triggerUB
  .

  Definition mem: ModSem.t := {|
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
