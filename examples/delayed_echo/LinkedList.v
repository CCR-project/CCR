Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import Mem1.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.









Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

(* void print_all(struct Node* ll) { *)
(*   if(ll) { *)
(*     printf("%d\t", ll->val); *)
(*     print_all(ll->next); *)
(*   } *)
(*   else { *)
(*     printf("\n"); *)
(*   } *)
(* } *)

  Definition print_allF_parg (varg: list val): option (block * ptrofs) :=
    match varg with
    | [Vptr b ofs] => Some (b, ofs)
    | _ => None
    end.

  (* Definition print_allF: Any.t -> itree Es Any.t := *)
  (*   fun varg => `varg: list val <- varg↓ǃ;; *)
  (*     '(blk, ofs) <- (print_allF_parg varg)?;; *)
  (*     b <- trigger (Call "cmp" [Vptr blk ofs; Vnullptr]↑);; `b: bool <- b↓ǃ;; *)
  (*     if b *)
  (*     then ( *)
  (*         let addr_v    := Vptr blk ofs in *)
  (*         let addr_next := Vptr blk (ofs + 1) in *)
  (*         v <- trigger (Call "load" [addr_v]↑);; `v: val <- v↓ǃ;; *)
  (*         (trigger (Syscall "printf" [v]));; *)
  (*         next <- trigger (Call "load" [addr_next]↑);; `next: val <- next↓ǃ;; *)
  (*         trigger (Call "print_all" [next]↑);; Ret Vundef↑ *)
  (*       ) *)
  (*     else (trigger (Syscall "printf_newline_todo" []));; Ret Vundef↑ *)
  (* . *)

  Definition print_allF: list val -> itree Es val :=
    fun varg =>
      '(blk, ofs) <- (print_allF_parg varg)?;;
      `b: bool <- (ccall "cmp" [Vptr blk ofs; Vnullptr]);;
      if b
      then (
          let addr_v    := Vptr blk ofs in
          let addr_next := Vptr blk (ofs + 1) in
          `v: val <- (ccall "load" [addr_v]);;
          (trigger (Syscall "printf" [v]));;
          `next: val <- (ccall "load" [addr_next]);;
          (ccall "print_all" [next])
        )
      else (trigger (Syscall "printf_newline_todo" []))
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
      `_: val        <- (ccall "print_all" [new_node]);;
      Ret vret
  .

  Definition LinkedListSem: ModSem.t := {|
    ModSem.fnsems := [("printf_all", cfun print_allF); ("pushF", cfun pushF)];
    ModSem.initial_mrs := [("LinkedList", (ε, unit↑))];
  |}
  .

  Definition LinkedList: Mod.t := {|
    Mod.get_modsem := fun _ => LinkedListSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.

(****** TODO: instead of syscall, use call to IO module (this makes the example more interesting).
 Also, it will probably make extraction easier. ********)
