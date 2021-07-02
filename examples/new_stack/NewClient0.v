Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import TODOYJ.
Require Import OpenDef.

Set Implicit Arguments.



Definition getintF {E} `{eventE -< E}:  list val -> itree E val :=
  fun args =>
    _ <- (pargs [] args)?;;
    trigger (Syscall "scan" [] top1).

Definition putintF {E} `{eventE -< E}: list val -> itree E val :=
  fun varg =>
    `v: val <- (pargs [Tuntyped] varg)?;;
    (if (wf_val v) then Ret tt else triggerUB);;; (* TODO: make notation *)
    trigger (Syscall "print" varg top1);;;
    Ret Vundef
.


Section PROOF.

  Context `{Σ: GRA.t}.

  Definition ClientSem: ModSem.t := {|
    ModSem.fnsems := [("getint", cfunU getintF); ("putint", cfunU putintF)];
    ModSem.mn := "Client";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Client: Mod.t := {|
    Mod.get_modsem := fun _ => ClientSem;
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.
