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
      `h: val    <- (ccall "new" ([]: list val));;
      `_: val    <- (ccall "input" ([h]: list val));;
      `_: val    <- (ccall "output" ([h]: list val));;
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
      `n: val    <- (ccall "getint" ([]: list val));;
      if (dec n (Vint INT_MIN))
      then Ret Vundef
      else
        `_: val    <- (ccall "push" ([h; n]: list val));;
        `_: val    <- (ccall "input" ([h]: list val));;
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
      `n: val    <- (ccall "pop" ([h]: list val));;
      if (dec n (Vint INT_MIN))
      then Ret Vundef
      else
        `_: val    <- (ccall "putint" ([n]: list val));;
        `_: val    <- (ccall "output" ([h]: list val));;
        Ret Vundef
  .

  Definition EchoSem: ModSem.t := {|
    ModSem.fnsems := [("echo", cfun echo_body); ("input", cfun input_body); ("output", cfun output_body)];
    ModSem.mn := "Echo";
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Echo: Mod.t := {|
    Mod.get_modsem := fun _ => EchoSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
