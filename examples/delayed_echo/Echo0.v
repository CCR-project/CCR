Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Stack1.
Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.






Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  (*** struct Node* my_list = NULL; ***)

(***
void echo() {
  int n = in();
  if(n == -1) {
    echo_finish();
    return;
  }
  my_list = push(my_list, n);
  echo();
}
***)

  Definition is_minus_one (v: val): bool :=
    match v with
    | Vint i => dec i (- 1)%Z
    | _ => false
    end
  .

  Definition echoF: list val -> itree Es val :=
    fun _ =>
      `n: val    <- (ccall "getint" ([]: list val));;
      if is_minus_one n
      then `_: val <- (ccall "echo_finish"  ([]: list val));; Ret Vundef
      else
        my_list0 <- trigger (PGet);;
        `my_list0: val <- my_list0↓?;;
        `my_list1: val <- (ccall "push" [my_list0; n]);;
        trigger(PPut my_list1↑);;
        `_: val <- ccall "echo" ([]: list val);;
        Ret Vundef
  .

(***
void echo_finish() {
  if(my_list) {
    int #n = mmalloc(sizeof(int));
    my_list = pop2(my_list, n);
    putint(#n);
    echo_finish();
  }
}
***)

  Definition echo_finishF: list val -> itree Es val :=
    fun _ =>
      my_list0 <- trigger (PGet);; `my_list0: val <- my_list0↓?;;
      if is_zero my_list0
      then Ret Vundef
      else (
          `nref: val     <- (ccall "malloc" ([Vint 1%Z]));;
          `my_list1: val <- (ccall "pop2" ([my_list0; nref]));;
          trigger (PPut my_list1↑);;
          `n: val        <- (ccall "load" ([nref]));;
          `_: val        <- (ccall "putint" ([n]));;
          `_: val        <- (ccall "echo_finish" ([]: list val));;
          Ret Vundef
        )
  .

  Definition EchoSem: ModSem.t := {|
    ModSem.fnsems := [("echo", cfun echoF); ("echo_finish", cfun echo_finishF)];
    ModSem.mn := "Echo";
    ModSem.initial_mr := ε;
    ModSem.initial_st := Vnullptr↑;
  |}
  .

  Definition Echo: Mod.t := {|
    Mod.get_modsem := fun _ => EchoSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
