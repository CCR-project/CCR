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



(*** TODO: move to TODOYJ ***)
Definition resum_ktr A E F `{E -< F}: ktree E A ~> ktree F A := fun _ ktr a => interp (fun _ e => trigger e) (ktr a).



Definition out_parg: list val -> option val :=
  fun varg =>
    match varg with
    | [v] => Some v
    | _ => None
    end
.


(* Parameter inF: list val -> itree eventE val. *)
(* Parameter outF: list val -> itree eventE val. *)

(* Extract Constant inF => "___MINKI_DOTHIS___?????????". *)
(* Extract Constant outF => "___MINKI_DOTHIS___?????????". *)


Definition inF:  list val -> itree eventE val :=
  fun _ => trigger (Syscall "scanf" []).

Definition outF: list val -> itree eventE val :=
  fun varg =>
    `v: val <- (out_parg varg)?;;
    trigger (Syscall "printf" varg);;
    Ret Vundef
.


Section PROOF.

  Context `{Σ: GRA.t}.

  Definition ClientSem: ModSem.t := {|
    ModSem.fnsems := [("in", cfun (resum_ktr inF)); ("out", cfun (resum_ktr outF))];
    ModSem.initial_mrs := [("Client", (ε, tt↑))];
  |}
  .

  Definition Client: Mod.t := {|
    Mod.get_modsem := fun _ => ClientSem;
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.
