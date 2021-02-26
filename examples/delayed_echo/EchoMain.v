Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



(*** TODO: rename ccall into call; ***)
(*** TODO: move this to TODOYJ ***)
Definition hcall {X Y} (fn: gname) (varg: X): itree (hCallE +' pE +' eventE) Y :=
  vret <- trigger (hCall false fn varg↑);; vret <- vret↓ǃ;; Ret vret.


Section PROOF.

  Context `{Σ: GRA.t}.

  Definition main_body: list val -> itree (hCallE +' pE +' eventE) val :=
    fun _ =>
      `n: val <- (hcall "echo" ([]: list val));;
      Ret Vundef
  .

  Let main_spec:        fspec := (mk_simple "Main" (X:=unit) (fun _ _ o _ => o = ord_top) (top3)).

  Definition MainStb: list (gname * fspec) :=
    [("main", main_spec)]
  .

  Definition MainSbtb: list (gname * fspecbody) :=
    [("main", mk_specbody main_spec main_body)]
  .

  Definition MainSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fsb) => (fn, fun_to_tgt MainStb fn fsb)) MainSbtb;
    ModSem.initial_mrs := [("Main", (ε, ([]: list val)↑))];
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
