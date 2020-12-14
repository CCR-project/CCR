Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import Events.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare ModSem.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.









Section CANCEL.

  Context `{Σ: GRA.t}.

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

  Definition body_to_tgt (body: list val -> itree (hCallE +' eventE) val): list val -> itree Es val :=
    fun varg => interp_hCallE_tgt (body varg)
  .



  Definition handle_hCallE_src: hCallE ~> itree Es :=
    fun _ '(hCall fn varg) => trigger (Call fn varg)
  .

  Definition interp_hCallE_src: itree (hCallE +' eventE) ~> itree Es :=
    interp (case_ (bif:=sum1) handle_hCallE_tgt
                  ((fun T X => trigger X): eventE ~> itree Es))
  .

  Definition body_to_src (body: list val -> itree (hCallE +' eventE) val): list val -> itree Es val :=
    fun varg => interp_hCallE_src (body varg)
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
    ModSem.initial_mrs := List.map (map_snd (fun _ => ε)) ms_tgt.(ModSem.initial_mrs);
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
