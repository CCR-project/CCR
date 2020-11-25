Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Generalizable Variables E R A B C X Y Z GRA.

Set Implicit Arguments.



Instance points_to: RA.t := RA.pointwise block (RA.pointwise Z (RA.agree (unit + val))).
Compute (RA.car).

Definition own {GRA: GRA.t} (whole a: URA.car (t:=GRA)): Prop := URA.extends a whole.


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
1. Write it with assume/guarantee.
2. Use Rely/Guarantee in simulation technique.

<<<<<<<<<<<<<< Maybe it is better to give function call stack for each mname,
               for better modularity & less cognitive overhead >>>>>>>>>>>>>>>>>

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



Local Notation "blk#ofs |-> v" := blk 
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.

Section PROOF.
  Variable points_to: URA.t.
  Context `{@GRA.inG points_to GRA}.
Definition mem: ModSem.t
End PROOF.
