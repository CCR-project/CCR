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




(* Definition until (n: nat): list nat := mapi (fun n _ => n) (List.repeat tt n). *)



(** TODO: move to PCM.v **)
Declare Scope ra_scope.
Delimit Scope ra_scope with ra.
Notation " K ==> V' " := (RA.pointwise K V'): ra_scope.



Let _memRA: URA.t := (block ==> Z ==> (RA.excl val))%ra.
Compute (URA.car (t:=_memRA)).
Instance memRA: URA.t := URA.auth _memRA.
Compute (URA.car).

Definition points_to (loc: block * Z) (v: val): URA.car :=
  let (b, ofs) := loc in
  URA.white (M:=_memRA)
            (inl (fun _b _ofs => if (dec _b b) && (dec _ofs ofs) then Some v else None)).

(* Definition own {GRA: GRA.t} (whole a: URA.car (t:=GRA)): Prop := URA.extends a whole. *)

Notation "loc |-> v" := (points_to loc v) (at level 20).




Section PROOF.
  Context `{@GRA.inG memRA Σ}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.

  Definition mem_inv: Σ -> Prop :=
    fun mr0 => exists mem0, mr0 = GRA.padding (URA.black (M:=_memRA) (inl mem0)).

  Definition allocF: list val -> itree Es val :=
    fun varg =>
      sz <- trigger (Take nat);;
      assume(varg = [Vint (Z.of_nat sz)]);;
      (HoareFun "mem" mem_inv
                (top1)
                (fun _ rret => exists b,
                     rret = GRA.padding (fold_left URA.add (mapi (fun n _ => (b, Z.of_nat n) |-> (Vint 0))
                                                                 (List.repeat tt sz)) URA.unit))
                (Ret tt))
  .

  Definition freeF: list val -> itree Es val :=
    fun varg =>
      '(b, ofs) <- trigger (Take _);;
      assume(varg = [Vptr b ofs]);;
      (HoareFun "mem" mem_inv
                (fun rarg => exists v, rarg = (GRA.padding ((b, ofs) |-> v)))
                (top2)
                (Ret tt))
  .

  Definition mem: ModSem.t := {|
    ModSem.fnsems := [("alloc", allocF)];
    ModSem.initial_mrs := [("mem", GRA.padding (URA.black (M:=_memRA) (inr tt)))];
  |}
  .
End PROOF.
