Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import HeapsortHeader.
Require Import Heapsort1.

Section HEAPSORTMAIN.
  
  Definition example : list Z := [7;4;5;3;1;6;0;3;6;8;1;6;8;4;7;9;2;5;7]%Z.

  Definition main_body : () -> itree Es () :=
    fun _ =>
      ys <- trigger (Call "heapsort" example↑);;
      _ <- trigger (Syscall "print" ys top1);;
      Ret tt.

  Definition MainSem : ModSem.t := {|
    ModSem.fnsems := [("main", cfunU main_body)];
    ModSem.mn := "Main";
    ModSem.initial_st := tt↑;
  |}.
                           
  Definition Main : Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := Sk.unit;
  |}.

End HEAPSORTMAIN.

Section EXTRACT.

  Definition heapsort_main1 := ModSemL.initial_itr (ModL.enclose (Mod.add_list [Heapsort; Main])) None.

End EXTRACT.
