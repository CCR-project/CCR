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



Require Import Mem1 Client1.

Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Definition MemMain1: Mod.t := Mod.add Mem Main.

  Definition MainSem2: ModSem.t := {|
    ModSem.fnsems := List.map (map_snd fun_to_src) MainStb;
    ModSem.initial_mrs := [("Main", ε)];
  |}
  .

  Definition Main2: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem2;
    (* Mod.sk := List.map fst MainStb; *)
    Mod.sk := Sk.unit;
  |}
  .

  Definition MemSem2: ModSem.t := {|
    ModSem.fnsems := List.map (map_snd fun_to_src) MemStb;
    ModSem.initial_mrs := [("Mem", ε)];
  |}
  .

  Definition Mem2: Mod.t := {|
    Mod.get_modsem := fun _ => MemSem2; (*** TODO: we need proper handling of function pointers ***)
    (* Mod.sk := List.map fst MemStb; *)
    Mod.sk := Sk.unit;
  |}
  .

  Definition MemMain2: Mod.t := Mod.add Mem2 Main2.

  Theorem correct: Beh.of_program (Mod.interp MemMain1) <1= Beh.of_program (Mod.interp MemMain2).
  Proof.
    ii.
    set (global_stb:=MemStb++MainStb).
    (* clearbody global_stb. *)
    Local Opaque MemStb.
    Local Opaque Mem1.MemStb.
    Local Opaque MainStb.
    eapply adequacy_type with (stb:=global_stb) in PR. cbn in *.
    rp; try apply PR; cycle 1.
    { refl. }
    clear PR. f_equal.
  Qed.

End PROOF.
