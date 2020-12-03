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

  Definition mem_inv: Σ -> Prop := admit "".

  Definition HoareFun
             (mn: mname)
             (I: URA.car -> Prop)
             (P: URA.car -> Prop)
             (Q: val -> URA.car -> Prop)
             (f: itree Es unit): itree Es val :=
    rarg <- trigger (Take URA.car);; trigger (Forge rarg);; (*** virtual resource passing ***)
    assume(P rarg);; (*** precondition ***)
    mopen <- trigger (MGet mn);; assume(I mopen);; (*** opening the invariant ***)

    f;; (*** it is a "rudiment": we don't remove extcalls because of termination-sensitivity ***)
    vret <- trigger (Choose _);;

    mclose <- trigger (MGet mn);; guarantee(I mclose);; (*** closing the invariant ***)
    rret <- trigger (Choose URA.car);; guarantee(Q vret rret);; (*** postcondition ***)
    trigger (Discard rret);; (*** virtual resource passing ***)

    Ret vret (*** return ***)
  .


  Section PLAYGROUND.

    (*** Q can mention the resource in the P ***)
    Definition HoareFun_sophis
               (mn: mname)
               (I: URA.car -> Prop)
               (P: URA.car -> Prop)
               (Q: URA.car -> val -> URA.car -> Prop)
               (f: itree Es unit): itree Es val :=
      rarg <- trigger (Take URA.car);; trigger (Forge rarg);; (*** virtual resource passing ***)
      assume(P rarg);; (*** precondition ***)
      mopen <- trigger (MGet mn);; assume(I mopen);; (*** opening the invariant ***)

      f;; (*** it is a "rudiment": we don't remove extcalls because of termination-sensitivity ***)
      vret <- trigger (Choose _);;

      mclose <- trigger (MGet mn);; guarantee(I mclose);; (*** closing the invariant ***)
      rret <- trigger (Choose URA.car);; guarantee(Q rarg vret rret);; (*** postcondition ***)
      trigger (Discard rret);; (*** virtual resource passing ***)

      Ret vret (*** return ***)
    .

    Definition HoareFun_sophis2
               (mn: mname)
               (I: URA.car -> Prop)
               (P: URA.car -> Prop)
               (Q: URA.car -> val -> URA.car -> Prop)
               (f: itree Es unit): itree Es val :=
      _rarg_ <- trigger (Take _);;
      HoareFun mn I (P /1\ (eq _rarg_)) (Q _rarg_) f
    .

  End PLAYGROUND.

  Definition allocF: list val -> itree Es val :=
    fun varg =>
    sz <- (allocF_parg varg)?;;
    HoareFun "mem" mem_inv (top1)
    (fun _ rret => exists b, forall ofs (RNG: 0 <= ofs < sz),
           GRA.padding (points_to (b, 0) (Vint 0))
    )
    (Ret tt)
  .

  Definition mem: ModSem.t := {|
    (* ModSem.sk := ["alloc" ; "store" ; "load" ; "free"]; *)
    (* ModSem.sem := *)
    (*   fun _ '(Call fname args) => *)
    (*     if dec fname "alloc" *)
    (*     then allocF args *)
    (*     else triggerUB; *)
    ModSem.fnsems := [("alloc", allocF)];
    ModSem.initial_mrs := [("mem", GRA.padding (URA.black (M:=_memRA) (inr tt)))];
  |}
  .
End PROOF.
