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



Require Import Mem1 Main1.

Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Definition MemMain1: Mod.t := Mod.add Mem Main.

  (* Definition MainSem2: ModSem.t := {| *)
  (*   ModSem.fnsems := List.map (map_snd fun_to_src) MainStb; *)
  (*   ModSem.initial_mrs := [("Main", ε)]; *)
  (* |} *)
  (* . *)

  (* Definition Main2: Mod.t := {| *)
  (*   Mod.get_modsem := fun _ => MainSem2; *)
  (*   Mod.sk := Sk.unit; *)
  (* |} *)
  (* . *)

  (* Definition MemSem2: ModSem.t := {| *)
  (*   ModSem.fnsems := List.map (map_snd fun_to_src) MemStb; *)
  (*   ModSem.initial_mrs := [("Mem", ε)]; *)
  (* |} *)
  (* . *)

  (* Definition Mem2: Mod.t := {| *)
  (*   Mod.get_modsem := fun _ => MemSem2; (*** TODO: we need proper handling of function pointers ***) *)
  (*   Mod.sk := Sk.unit; *)
  (* |} *)
  (* . *)

  (* Definition MemMain2: Mod.t := Mod.add Mem2 Main2. *)

  Definition MemMain2: Mod.t := {|
    Mod.get_modsem := fun _ => {|
        ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_src body)) (MemFtb ++ MainFtb);
        (* ModSem.initial_mrs := [("Mem", ε) ; ("Main", ε)]; *)
        ModSem.initial_mrs := [];
      |};
    Mod.sk := Sk.unit;
  |}
  .

  Theorem correct: Beh.of_program (Mod.interp MemMain1) <1= Beh.of_program (Mod.interp MemMain2).
  Proof.
    ii.
    set (global_ftb:=MemFtb++MainFtb).
    (* clearbody global_stb. *)
    Local Opaque MemStb.
    Local Opaque Mem1.MemStb.
    Local Opaque MainStb.
    eapply adequacy_type with (ftb:=global_ftb) in PR. cbn in *.
    rp; try apply PR; cycle 1.
    { refl. }
    clear PR. f_equal.
  Qed.

End PROOF.