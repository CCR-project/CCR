Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Mem1.
Require Import TODOYJ.
Require Import NewEchoHeader.

Set Implicit Arguments.






Section PROOF.

  Context `{Σ: GRA.t}.

  (* void echo() { *)
  (*   void* h = Stack.new(); *)
  (*   input(h); *)
  (*   output(h); *)
  (* } *)

  Definition echo_body: list val -> itree Es val :=
    fun args =>
      _ <- (pargs [] args)?;;
      `h: val    <- (ccallU "new" ([]: list val));;
      `_: val    <- (ccallU "input" ([h]: list val));;
      `_: val    <- (ccallU "output" ([h]: list val));;
      Ret Vundef
  .

  (* void echo_get(void* h) { *)
  (*   int n = IO.getint(); *)
  (*   if(n == INT_MIN) return; *)
  (*   Stack.push(h, n); *)
  (*   echo_get(h); *)
  (* } *)

  Definition input_body: list val -> itree Es val :=
    fun args =>
      h <- (pargs [Tuntyped] args)?;;
      `n: val    <- (ccallU "getint" ([]: list val));;
      assume((wf_val n) /\ (match n with | Vint _ => True | _ => False end));;;
      if (dec n (Vint (- 1)))
      then Ret Vundef
      else
        `_: val    <- (ccallU "push" ([h; n]: list val));;
        `_: val    <- (ccallU "input" ([h]: list val));;
        Ret Vundef
  .

  (* void echo_put(void* h) { *)
  (*   int n = Stack.pop(h); *)
  (*   if(n == INT_MIN) return; *)
  (*   IO.putint(n); *)
  (*   echo_put(h); *)
  (* } *)

  Definition output_body: list val -> itree Es val :=
    fun args =>
      h <- (pargs [Tuntyped] args)?;;
      `n: val    <- (ccallU "pop" ([h]: list val));;
      assume((wf_val n) /\ (match n with | Vint _ => True | _ => False end));;;
      if (dec n (Vint (- 1)))
      then Ret Vundef
      else
        `_: val    <- (ccallU "putint" ([n]: list val));;
        `_: val    <- (ccallU "output" ([h]: list val));;
        Ret Vundef
  .

  Definition EchoSem: ModSem.t := {|
    ModSem.fnsems := [("echo", cfunU echo_body); ("input", cfunU input_body); ("output", cfunU output_body)];
    ModSem.mn := "Echo";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Echo: Mod.t := {|
    Mod.get_modsem := fun _ => EchoSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
