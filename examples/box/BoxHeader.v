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
Set Typeclasses Depth 5.



Let _boxRA: URA.t := RA.excl Z.
Compute (URA.car (t:=_boxRA)).
Instance boxRA: URA.t := URA.auth _boxRA.
Compute (URA.car).

Section PROOF.

  Context `{@GRA.inG boxRA Σ}.
  Definition client (x: Z): Σ := (GRA.padding (URA.white (M:=_boxRA) (inl (Some x)))).
  Definition library (x: Z): Σ := (GRA.padding (URA.black (M:=_boxRA) (inl (Some x)))).

  Definition BoxStb: list (gname * fspec) :=
    [("get", mk "Box"
                (fun x varg rarg => varg = [] /\ rarg = client x)
                (fun x vret rret => vret = Vint x /\ rret = client x)) ;
    ("set", mk "Box"
               (fun x varg rarg => varg = [Vint x] /\ exists x_old, rarg = client x_old)
               (fun x vret rret => rret = client x))
    ]
  .

  Definition MainStb: list (gname * fspec) :=
    [("main", mk "Main" (X:=unit) top3 top3)].

  Definition AddStb: list (gname * fspec) :=
    [("add", mk "Add"
                (fun x varg rarg => varg = [] /\ rarg = client x)
                (fun x vret rret => rret = client (Z.add x 1)))
    ].

End PROOF.

  (* Let memRA: URA.t := (RA.excl Z). *)
  (* Context `{@GRA.inG memRA Σ}. *)
  (* Let GURA: URA.t := GRA.to_URA Σ. *)
  (* Local Existing Instance GURA. *)
