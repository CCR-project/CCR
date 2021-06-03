Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Mem1.
Require Import TODO TODOYJ.

Set Implicit Arguments.





Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

(***
(Replaced asterisk with # because of coq-mode's parsing)
int pop(struct Node## llref) {
  if(#llref) {
    int v = (#llref)->val;
    struct Node* next = (#llref)->next;
    free(#llref);
    (#llref) = next;
    return v;
  }
  return -1;
}
***)

  Definition popF: list val -> itree Es val :=
    fun varg =>
      `llref: val <- (pargs [Tuntyped] varg)?;;
      `ll: val    <- (ccall "load" [llref]);;
      `b: val     <- (ccall "cmp"  [ll; Vnullptr]);;
      if is_zero b
      then (
          '(blk, ofs) <- (parg Tptr ll)?;;
          let addr_val  := Vptr blk ofs in
          let addr_next := Vptr blk (ofs + 1) in
          `v: val    <- (ccall "load"  [addr_val]);;
          (* `_: val    <- (ccall "debug" [v]);; *)
          `next: val <- (ccall "load"  [addr_next]);;
          `_: val    <- (ccall "free"  [addr_val]);;
          `_: val    <- (ccall "free"  [addr_next]);; (*** change "free"s specification ***)
          `_: val    <- (ccall "store" [llref; next]);;
          Ret v
        )
      else Ret (Vint (- 1))
  .

(* struct Node* push(struct Node* ll, int x) { *)
(*   struct Node* new_node = malloc(sizeof(struct Node)); *)
(*   new_node->val = x; *)
(*   new_node->next = ll; *)
(*   printf("[DEBUG]: "); *)
(*   print_all(new_node); *)
(*   return new_node; *)
(* } *)

  Definition pushF: list val -> itree Es val :=
    fun varg =>
      '(node, v)     <- (pargs [Tuntyped; Tuntyped] varg)?;;
      `_: val        <- (ccall "debug" [v]);;
      `new_node: val <- (ccall "alloc" [Vint 2]);;
      addr_v         <- (vadd new_node (Vint 0))?;;
      addr_next      <- (vadd new_node (Vint 1))?;;
      `_: val        <- (ccall "store" [addr_v;    v]);;
      `vret: val     <- (ccall "store" [addr_next; node]);;
      Ret addr_v
  .

  Definition StackSem: ModSem.t := {|
    ModSem.fnsems := [("pop", cfun popF); ("push", cfun pushF)];
    ModSem.mn := "Stack";
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Stack: Mod.t := {|
    Mod.get_modsem := fun _ => StackSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
