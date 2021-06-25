Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import TODOYJ.

Set Implicit Arguments.





(* Parameter inF: list val -> itree eventE val. *)
(* Parameter putintF: list val -> itree eventE val. *)

(* Extract Constant inF => "___MINKI_DOTHIS___?????????". *)
(* Extract Constant putintF => "___MINKI_DOTHIS___?????????". *)


Definition getintF {E} `{eventE -< E}:  list val -> itree E val :=
  fun _ => trigger (Syscall "scanf" [] top1).

Definition putintF {E} `{eventE -< E}: list val -> itree E val :=
  fun varg =>
    `v: val <- (pargs [Tuntyped] varg)?;;
    trigger (Syscall "printf" varg top1);;;
    Ret Vundef
.


Section PROOF.

  Context `{Σ: GRA.t}.

  Definition ClientSem: ModSem.t := {|
    ModSem.fnsems := [("getint", cfun getintF); ("putint", cfun putintF)];
    ModSem.mn := "Client";
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Client: Mod.t := {|
    Mod.get_modsem := fun _ => ClientSem;
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.
