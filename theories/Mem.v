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

Global Program Instance Z_Dec: Dec Z. Next Obligation. apply Z.eq_dec. Defined.








Let _memRA: URA.t := (RA.pointwise block (RA.pointwise Z (RA.excl val))).
Instance memRA: URA.t := URA.auth _memRA.
Compute (URA.car).

Definition points_to (loc: block * Z) (v: val): URA.car :=
  let (b, ofs) := loc in
  URA.white (M:=_memRA)
            (inl (fun _b _ofs => if (dec _b b) && (dec _ofs ofs) then Some v else None)).

Definition own {GRA: GRA.t} (whole a: URA.car (t:=GRA)): Prop := URA.extends a whole.

Notation "loc |-> v" := (points_to loc v) (at level 20).

(***
r <- Take;;
FAdd(r);; <-------------------------- illegal in some sense
assume((blk |-> R) <= r \/ (blk |-> G) <= r \/ (blk |-> B) <= r);;  (iProp???)
meta-assume(list mname(for modular reasoning), current stackframe);;

r <- Choose;;
FSub(r);; := Get;; Choose;; guarantee;; Set;;
guarantee(blk |-> v <= r);;
(call f);;
r <- Take;;
FAdd(r);; <-------------------------- illegal in some sense
assume(some_other_resource <= r);;
meta-assume(list mname(for modular reasoning), current stackframe);;

r <- Choose;;
FSub(r);;
guarantee(blk |-> v <= r);;
***)

(***
HoareFun := FPush;; [[boilerplate]] real_code [[boilerplate]] FPop;;
real_code := itree, using HoareCall, not benign call
             calling meta-assume is allowed. "list mname" is hard-coded in the module.
HoareCall := [[boilerplate]] call [[boilerplate]]

the illegal update (FAdd(r)) is only allowed in boilerplate code.
FPush/FPop is only allowed in boilerplate code.
***)

(***
FPush
  r <- Take;
  assume(P /\ IP r);
  cur <- FGet; FPut (cur * r);



    r <- Choose;
    guarantee(P /\ IP r);
    cur <- FGet; cur' <- Choose; guarantee(cur' * r = cur); FPut cur';
      call;
    ...
    ...
    ...

  ...
  ...
  ...
FPop

NB: this "discarded" resource is *actually* discarded; the user can't access it in the real_code
***)

(***
Where does the `Function Locality` appear in our scenario?
Use Rely/Guarantee in simulation technique.



FPush
  r <- Take;
  assume(P /\ IP r);
  cur <- FGet; FPut (cur * r);



    r <- Choose;
    guarantee(P /\ IP r);
    cur <- FGet; cur' <- Choose; guarantee(cur' * r = cur); FPut cur';
      call;
    ...
    ...
    ...

  ...
  ...
  ...
FPop

***)
Section PROOF.
  (* Context {myRA} `{@GRA.inG myRA Σ}. *)
  Context {Σ: GRA.t}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.
  Variable mn: mname.

  Definition FAdd `{fnE -< E} (r: URA.car): itree E unit :=
    rcur <- trigger (FGet);; trigger (FPut (URA.add rcur r))
  .

  Definition FSub `{fnE -< E} `{eventE -< E} (r: URA.car): itree E unit :=
    rcur <- trigger (FGet);;
    rnext <- trigger (Choose _);;
    guarantee(rcur = URA.add rnext r);;
    trigger (FPut rnext)
  .

  (*** think of Box, UnionFind, etc. ***)
  (* Definition transfer `{fnE -< E} `{eventE -< E} (r: URA.car): itree E unit := *)
  (*   rcur ... *)
  (* . *)

  Definition HoareFun
             (P: URA.car -> URA.car -> list val -> Prop)
             (Q: URA.car -> URA.car -> list val -> URA.car -> URA.car -> val -> Prop)
             (f: list val -> itree (callE +' mdE +' fnE +' eventE) val):
    list val -> itree (callE +' mdE +' fnE +' eventE) val :=
    fun vs0 =>
      ld0 <- trigger (MGet mn);;
      r <- trigger (Take URA.car);;
      assume(P ld0 r vs0);;
      FAdd r;;

      assume(<<WTY: URA.wf (URA.add ld0 r)>>);;
      vr <- (f vs0);;

      ld1 <- trigger (MGet mn);;
      rr <- trigger (Choose URA.car);;
      guarantee(Q ld0 r vs0 ld1 rr vr);;
      FSub rr;;
      Ret vr
  .

  Definition HoareCall
             (P: URA.car -> URA.car -> list val -> Prop)
             (Q: URA.car -> URA.car -> list val -> URA.car -> URA.car -> val -> Prop):
    fname -> list val -> itree (callE +' mdE +' fnE +' eventE) val :=
    fun fn vs0 =>
      ld0 <- trigger (MGet mn);;
      r <- trigger (Choose URA.car);;
      FSub r;;
      guarantee(P ld0 r vs0);;

      vr <- trigger (Call fn vs0);;

      Ret vr
  .

End PROOF.

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

  Definition allocF (args: list val): itree (callE +' mdE +' fnE +' eventE) val :=
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
