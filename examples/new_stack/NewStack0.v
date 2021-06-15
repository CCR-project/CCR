Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Mem1.
Require Import TODOYJ.

Set Implicit Arguments.





Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  (* def new(): Ptr *)
  (*   Ptr stk = alloc(1); *)
  (*   return stk *)

  Definition newF: list val -> itree Es val :=
    fun args =>
      _ <- (pargs [] args)?;;
      `new_node: val  <- (ccall "alloc" [Vint 1]);;
      `_: val         <- (ccall "store" [new_node; Vnullptr]);;
      Ret new_node
  .

  (* def pop(Ptr stk): Int64 *)
  (*   let hd := load(stk, 0); *)
  (*   if(ptrcmp(hd, NULL) != 0) { *)
  (*     let v    := load(hd, 0); *)
  (*     let next := load(hd, 1); *)
  (*     free(hd, 2); *)
  (*     store(stk, 0, next); *)
  (*     debug(false, v); *)
  (*     return v *)
  (*   } *)
  (*   return -1 *)

  Definition popF: list val -> itree Es val :=
    fun args =>
      `stk: val <- (pargs [Tuntyped] args)?;;
      `hd: val  <- (ccall "load" [stk]);;
      `b: val   <- (ccall "cmp"  [hd; Vnullptr]);;
      if is_zero b
      then (
          let addr_val    := hd in
          `addr_next: val <- (vadd hd (Vint 8))?;;
          `v: val         <- (ccall "load"  [addr_val]);;
          `next: val      <- (ccall "load"  [addr_next]);;
          `_: val         <- (ccall "free"  [addr_val]);;
          `_: val         <- (ccall "free"  [addr_next]);;
          `_: val         <- (ccall "store" [stk; next]);;
          `_: val         <- (ccall "debug" [Vint 0; v]);;
          Ret v
        )
      else Ret (Vint (- 1))
  .

  (* def push(Ptr stk, Int64 n): Unit *)
  (*   let new_node := alloc(2); *)
  (*   store(new_node, 0, n); *)
  (*   let hd := load(stk, 0); *)
  (*   store(new_node, 1, hd); *)
  (*   store(stk, 0, new_node); *)
  (*   debug(true, n); *)
  (*   return () *)

  Definition pushF: list val -> itree Es val :=
    fun args =>
      '(stk, v)      <- (pargs [Tuntyped; Tuntyped] args)?;;
      `new_node: val <- (ccall "alloc" [Vint 2]);;
      let addr_val   := new_node in
      addr_next      <- (vadd new_node (Vint 8))?;;
      `hd: val       <- (ccall "load"  [stk]);;
      `_: val        <- (ccall "store" [addr_val;   v]);;
      `_: val        <- (ccall "store" [addr_next; hd]);;
      `_: val        <- (ccall "store" [stk; new_node]);;
      `_: val        <- (ccall "debug" [Vint 1; v]);;
      Ret Vundef
  .

  Definition StackSem: ModSem.t := {|
    ModSem.fnsems := [("new", cfun newF); ("pop", cfun popF); ("push", cfun pushF)];
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
