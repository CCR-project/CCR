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
  Context `{X: Type}. (*** a meta-variable ***)

  (* Definition HoareFun *)
  (*            (I: URA.car -> Prop) *)
  (*            (P: URA.car -> list val -> Prop) *)
  (*            (Q: URA.car -> list val -> URA.car -> val -> Prop) *)
  (*            (f: list val -> itree Es val): *)
  (*   list val -> itree Es val := *)
  (*   fun varg => *)
  (*     rarg <- trigger (Take URA.car);; trigger (Forge rarg);; (*** virtual resource passing ***) *)
  (*     assume(P rarg varg);; (*** precondition ***) *)
  (*     mopen <- trigger (MGet mn);; assume(I mopen);; (*** opening the invariant ***) *)

  (*     vret <- f varg;; (*** body ***) *)

  (*     mclose <- trigger (MGet mn);; guarantee(I mclose);; (*** closing the invariant ***) *)
  (*     rret <- trigger (Choose URA.car);; guarantee(Q rarg varg rret vret);; (*** postcondition ***) *)
  (*     trigger (Discard rret);; (*** virtual resource passing ***) *)

  (*     Ret vret (*** return ***) *)
  (* . *)

  Definition HoareFun
             (P: X -> list val -> Σ -> Prop)
             (Q: X -> val -> Σ -> Prop)
             (body: X -> list val -> itree Es val): list val -> itree Es val := fun varg =>
    x <- trigger (Take X);;
    rarg <- trigger (Take Σ);; trigger (Forge rarg);; (*** virtual resource passing ***)
    trigger (CheckWf mn);;
    assume(P x varg rarg);; (*** precondition ***)


    vret <- body x varg;; (*** "rudiment": we don't remove extcalls because of termination-sensitivity ***)

    '(mret, fret) <- trigger (Choose _);; trigger (Put mn mret fret);; (*** updating resources in an abstract way ***)
    rret <- trigger (Choose Σ);; guarantee(Q x vret rret);; (*** postcondition ***)
    trigger (Discard rret);; (*** virtual resource passing ***)

    Ret vret (*** return ***)
  .

  Definition HoareCall
             (P: X -> list val -> Σ -> Prop)
             (Q: X -> val -> Σ -> Prop):
    fname -> list val -> itree Es val :=
    fun fn varg =>
      '(marg, farg) <- trigger (Choose _);; trigger (Put mn marg farg);; (*** updating resources in an abstract way ***)
      rarg <- trigger (Choose Σ);; trigger (Discard rarg);; (*** virtual resource passing ***)
      x <- trigger (Choose X);;
      guarantee(P x varg rarg);; (*** precondition ***)

      vret <- trigger (Call fn varg);; (*** call ***)
      trigger (CheckWf mn);;

      rret <- trigger (Take Σ);; trigger (Forge rret);; (*** virtual resource passing ***)
      assume(Q x vret rret);; (*** postcondition ***)

      Ret vret (*** return to body ***)
  .

  (* Definition HoareFunCanceled *)
  (*            (body: itree Es unit): list val -> itree Es val := fun varg => *)
  (*   body;; (*** "rudiment": we don't remove extcalls because of termination-sensitivity ***) *)
  (*   vret <- trigger (Choose _);; *)
  (*   Ret vret (*** return ***) *)
  (* . *)

  (* Definition HoareCallCanceled: *)
  (*   fname -> list val -> itree Es val := *)
  (*   fun fn varg => *)
  (*     vret <- trigger (Call fn varg);; (*** call ***) *)
  (*     Ret vret (*** return to body ***) *)
  (* . *)

  (* Section PLAYGROUND. *)

  (*   (*** Q can mention the resource in the P ***) *)
  (*   Let HoareFun_sophis *)
  (*              (mn: mname) *)
  (*              (P: URA.car -> Prop) *)
  (*              (Q: URA.car -> val -> URA.car -> Prop) *)
  (*              (f: itree Es unit): itree Es val := *)
  (*     rarg <- trigger (Take URA.car);; trigger (Forge rarg);; (*** virtual resource passing ***) *)
  (*     assume(P rarg);; (*** precondition ***) *)
  (*     mopen <- trigger (MGet mn);; *)

  (*     f;; (*** it is a "rudiment": we don't remove extcalls because of termination-sensitivity ***) *)
  (*     vret <- trigger (Choose _);; *)

  (*     mclose <- trigger (MGet mn);; *)
  (*     rret <- trigger (Choose URA.car);; trigger (Discard rret);; (*** virtual resource passing ***) *)
  (*     guarantee(Q rarg vret rret);; (*** postcondition ***) *)

  (*     Ret vret (*** return ***) *)
  (*   . *)

  (*   Let HoareFun_sophis2 *)
  (*              (mn: mname) *)
  (*              (P: URA.car -> Prop) *)
  (*              (Q: URA.car -> val -> URA.car -> Prop) *)
  (*              (f: itree Es unit): itree Es val := *)
  (*     _rarg_ <- trigger (Take _);; *)
  (*     HoareFun mn (P /1\ (eq _rarg_)) (Q _rarg_) f *)
  (*   . *)

  (* End PLAYGROUND. *)




  (* Definition HoareCall *)
  (*            (I: URA.car -> Prop) *)
  (*            (P: URA.car -> list val -> Prop) *)
  (*            (Q: URA.car -> list val -> URA.car -> val -> Prop): *)
  (*   fname -> list val -> itree Es val := *)
  (*   fun fn varg => *)
  (*     mclose <- trigger (MGet mn);; guarantee(I mclose);; (*** closing the invariant ***) *)
  (*     rarg <- trigger (Choose URA.car);; guarantee(P rarg varg);; (*** precondition ***) *)
  (*     trigger (Discard rarg);; (*** virtual resource passing ***) *)

  (*     vret <- trigger (Call fn varg);; (*** call ***) *)

  (*     rret <- trigger (Take URA.car);; trigger (Forge rret);; (*** virtual resource passing ***) *)
  (*     assume(Q rarg varg rret vret);; (*** postcondition ***) *)
  (*     mopen <- trigger (MGet mn);; assume(I mopen);; (*** opening the invariant ***) *)

  (*     Ret vret (*** return to body ***) *)
  (* . *)



  (* Definition HoareFun *)
  (*            (INV: URA.car -> Prop) *)
  (*            (P: URA.car -> list val -> Prop) *)
  (*            (Q: URA.car -> list val -> URA.car -> val -> Prop) *)
  (*            (f: list val -> itree Es val): *)
  (*   list val -> itree Es val := *)
  (*   fun vs0 => *)
  (*     ld0 <- trigger (MGet mn);; *)
  (*     r <- trigger (Take URA.car);; *)
  (*     assume(P ld0 r vs0);; *)
  (*     FAdd r;; *)

  (*     assume(<<WTY: URA.wf (URA.add ld0 r)>>);; *)
  (*     vr <- (f vs0);; *)

  (*     ld1 <- trigger (MGet mn);; *)
  (*     rr <- trigger (Choose URA.car);; *)
  (*     guarantee(Q ld0 r vs0 ld1 rr vr);; *)
  (*     FSub rr;; *)
  (*     Ret vr *)
  (* . *)

  (* Definition HoareCall *)
  (*            (P: URA.car -> URA.car -> list val -> Prop) *)
  (*            (Q: URA.car -> URA.car -> list val -> URA.car -> URA.car -> val -> Prop): *)
  (*   fname -> list val -> itree (callE +' mdE +' fnE +' eventE) val := *)
  (*   fun fn vs0 => *)
  (*     ld0 <- trigger (MGet mn);; *)
  (*     r <- trigger (Choose URA.car);; *)
  (*     FSub r;; *)
  (*     guarantee(P ld0 r vs0);; *)

  (*     vr <- trigger (Call fn vs0);; *)

  (*     Ret vr *)
  (* . *)

End PROOF.















Definition map_fst A0 A1 B (f: A0 -> A1): (A0 * B) -> (A1 * B) := fun '(a, b) => (f a, b).
Definition map_snd A B0 B1 (f: B0 -> B1): (A * B0) -> (A * B1) := fun '(a, b) => (a, f b).
(*** TODO: Move to Coqlib. TODO: Somehow use case_ ??? ***)

Section CANCEL.

  Context `{Σ: GRA.t}.

  Variant hCallE: Type -> Type :=
  | hCall
      (* (mn: mname) *)
      (* (P: list val -> Σ -> Prop) (Q: list val -> Σ -> val -> Σ -> Prop) *)
      (fn: fname) (varg: list val): hCallE val
  .

  (*** spec table ***)
  Record funspec: Type := mk {
    mn: mname;
    X: Type; (*** a meta-variable ***)
    precond: X -> list val -> Σ -> Prop;
    postcond: X -> val -> Σ -> Prop;
    body: X -> list val -> itree (hCallE +' eventE) val;
  }
  .

  (* Variable stb: fname -> option funspec. *)
  (*** TODO: I wanted to use above definiton, but doing so makes defining ms_src hard ***)
  (*** We can fix this by making ModSem.fnsems to a function, but doing so will change the type of
       ModSem.add to predicate (t -> t -> t -> Prop), not function.
       - Maybe not. I thought one needed to check uniqueness of fname at the "add",
         but that might not be the case.
         We may define fnsems: string -> option (list val -> itree Es val).
         When adding two ms, it is pointwise addition, and addition of (option A) will yield None when both are Some.
 ***)
  (*** TODO: try above idea; if it fails, document it; and refactor below with alist ***)
  Variable stb: list (fname * funspec).

  Definition handle_hCallE_tgt: hCallE ~> itree Es :=
    fun _ '(hCall fn varg) =>
      match List.find (fun '(_fn, _) => dec fn _fn) stb with
      | Some (_, f) =>
        (HoareCall f.(mn) (f.(precond)) (f.(postcond)) fn varg)
      | None => triggerNB
      end
  .

  Definition interp_hCallE_tgt: itree (hCallE +' eventE) ~> itree Es :=
    interp (case_ (bif:=sum1) handle_hCallE_tgt
                  ((fun T X => trigger X): eventE ~> itree Es))
  .

  Definition body_to_tgt {X} (body: X -> list val -> itree (hCallE +' eventE) val): X -> list val -> itree Es val :=
    fun x varg => interp_hCallE_tgt (body x varg)
  .



  Definition handle_hCallE_src: hCallE ~> itree Es :=
    fun _ '(hCall fn varg) => trigger (Call fn varg)
  .

  Definition interp_hCallE_src: itree (hCallE +' eventE) ~> itree Es :=
    interp (case_ (bif:=sum1) handle_hCallE_src
                  ((fun T X => trigger X): eventE ~> itree Es))
  .

  Definition body_to_src {X} (body: X -> list val -> itree (hCallE +' eventE) val): X -> list val -> itree Es val :=
    fun x varg => interp_hCallE_src (body x varg)
  .
  Definition fun_to_tgt (f: funspec): (list val -> itree Es val) :=
    HoareFun f.(mn) (f.(precond)) (f.(postcond)) (body_to_tgt f.(body)).
  Definition fun_to_src (f: funspec): (list val -> itree Es val) := body_to_src f.(body).

(*** NOTE:
body can execute eventE events.
Notably, this implies it can also execute UB.
With this flexibility, the client code can naturally be included in our "type-checking" framework.
Also, note that body cannot execute "rE" on its own. This is intended.

NOTE: we can allow normal "callE" in the body too, but we need to ensure that it does not call "HoareFun".
If this feature is needed; we can extend it then. At the moment, I will only allow hCallE.
***)

  Variable md_tgt: Mod.t.
  Let ms_tgt: ModSem.t := (Mod.get_modsem md_tgt (Sk.load_skenv md_tgt.(Mod.sk))).

  Hypothesis WTY: ms_tgt.(ModSem.fnsems) = List.map (map_snd fun_to_tgt) stb.

  Definition ms_src: ModSem.t := {|
    ModSem.fnsems := List.map (map_snd fun_to_src) stb;
    (* ModSem.initial_mrs := List.map (map_snd (fun _ => ε)) ms_tgt.(ModSem.initial_mrs); *)
    ModSem.initial_mrs := [];
    (*** note: we don't use resources, so making everything as a unit ***)
  |}
  .

  Definition md_src: Mod.t := {|
    Mod.get_modsem := fun _ => ms_src;
    Mod.sk := Sk.unit;
    (*** It is already a whole-program, so we don't need Sk.t anymore. ***)
    (*** Note: Actually, md_tgt's sk could also have been unit, which looks a bit more uniform. ***)
  |}
  .

  Theorem adequacy_type: Beh.of_program (Mod.interp md_tgt) <1= Beh.of_program (Mod.interp md_src).
  Proof.
    admit "In the proof, we will need to show
(1) Choose/Take cancel
(2) assume/guarantee cancel
(3) src is resource unaware
(4) tgt is always wf (so CheckWf always succeeds)
".
  Qed.

End CANCEL.
