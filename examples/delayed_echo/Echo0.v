Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import LinkedList1.
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
  if(n == 0) {
    echo_finish();
    return;
  }
  my_list = push(my_list, n);
  echo();
}
***)

  Definition echoF: list val -> itree Es val :=
    fun _ =>
      `n: val    <- (ccall "in" ([]: list val));;
      if is_zero n
      then `_: val <- (ccall "echo_finish"  ([]: list val));; Ret Vundef
      else
        my_list0 <- trigger (PGet "Echo");;
        `my_list0: val <- my_list0↓?;;
        `my_list1: val <- (ccall "push" [my_list0; n]);;
        trigger(PPut "Echo" my_list1↑);;
        `_: val <- ccall "echo" ([]: list val);;
        Ret Vundef
  .

(***
void echo_finish() {
  int n = pop(&my_list);
  if(n == -1) return;
  else {
    out(n);
    echo_finish();
  }
}
***)

  Definition echo_finishF: list val -> itree Es val :=
    fun _ =>
      `n: val    <- (ccall "in" ([]: list val));;
      if is_zero n
      then `_: val <- (ccall "echo_finish"  ([]: list val));; Ret Vundef
      else
        my_list0 <- trigger (PGet "Echo");;
        `my_list0: val <- my_list0↓?;;
        `my_list1: val <- (ccall "push" [my_list0; n]);;
        trigger(PPut "Echo" my_list1↑);;
        `_: val <- ccall "echo" ([]: list val);;
        Ret Vundef
  .












  Definition is_zero (v: val): bool := match v with
                                       | Vint x => dec x 0%Z
                                       | Vptr 0 0%Z => true
                                       | _ => false
                                       end.

  Definition popF_parg: list val -> option val := (@hd_error _).
  Definition popF: list val -> itree Es val :=
    fun varg =>
      `llref: val <- (popF_parg varg)?;;
      `ll: val    <- (ccall "load" [llref]);;
      `b: val     <- (ccall "cmp"  [ll; Vnullptr]);;
      if is_zero b
      then (
          '(blk, ofs) <- (unptr ll)?;;
          let addr_val  := Vptr blk ofs in
          let addr_next := Vptr blk (ofs + 1) in
          `v: val    <- (ccall "load"  [addr_val]);;
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

  Definition pushF_parg (varg: list val): option (val * val) :=
    match varg with
    | [node; v] => Some (node, v)
    | _ => None
    end.

  Definition pushF: list val -> itree Es val :=
    fun varg =>
      '(node, v)     <- (pushF_parg varg)?;;
      `new_node: val <- (ccall "alloc" [Vint 2]);;
      addr_v         <- (vadd new_node (Vint 0))?;;
      addr_next      <- (vadd new_node (Vint 1))?;;
      `_: val        <- (ccall "store" [addr_v;    v]);;
      `vret: val     <- (ccall "store" [addr_next; node]);;
      (* `_: val        <- (ccall "print_all" [new_node]);; *)
      Ret addr_v
  .

  Definition LinkedListSem: ModSem.t := {|
    ModSem.fnsems := [("pop", cfun popF); ("push", cfun pushF)];
    ModSem.initial_mrs := [("LinkedList", (ε, tt↑))];
  |}
  .

  Definition LinkedList: Mod.t := {|
    Mod.get_modsem := fun _ => LinkedListSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
