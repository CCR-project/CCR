Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import OpenDef.

Set Implicit Arguments.



Definition getintF {E} `{eventE -< E}:  list val -> itree E val :=
  fun args =>
    _ <- (pargs [] args)?;;
    z <- trigger (Syscall "scan" (([]: list Z)↑) top1);; z <- z↓?;; Ret (Vint z).

Definition putintF {E} `{eventE -< E}: list val -> itree E val :=
  fun varg =>
    `v: Z <- (pargs [Tint] varg)?;;
    (if (intrange_64 v) then Ret tt else triggerUB);;; (* TODO: make notation *)
    z <- trigger (Syscall "print" [v]↑ top1);; `z: Z <- z↓?;;
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
    Mod.sk := [("getint", Sk.Gfun); ("putint", Sk.Gfun)];
  |}
  .

End PROOF.
