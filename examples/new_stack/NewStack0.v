Require Import Coqlib.
Require Import ImpPrelude.
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
      `new_node: val  <- (ccallU "alloc" [Vint 1]);;
      assume(wf_val new_node);;;
      `_: val         <- (ccallU "store" [new_node; Vnullptr]);;
      Ret new_node
  .

  (* def pop(Ptr stk): Int64 *)
  (*   let hd := load(stk, 0); *)
  (*   if(ptrcmp(hd, NULL) != 0) { *)
  (*     let v    := load(hd, 0); *)
  (*     let next := load(hd, 1); *)
  (*     free(hd, 2); *)
  (*     store(stk, 0, next); *)
  (*     return v *)
  (*   } *)
  (*   return -1 *)

  Definition popF: list val -> itree Es val :=
    fun args =>
      `stk: mblock <- (pargs [Tblk] args)?;;
      `hd: val  <- (ccallU "load" [Vptr stk 0]);;
      assume(wf_val hd);;;
      `b: val   <- (ccallU "cmp"  [hd; Vnullptr]);;
      assume((wf_val b) /\ (match b with | Vint _ => True | _ => False end));;;
      if dec (Vint 0) b
      then (
          let addr_val    := hd in
          assume (match addr_val with | Vptr _ 0 => True | _ => False end);;;
          `addr_next: val <- (vadd hd (Vint 8))?;;
          `v: val         <- (ccallU "load"  [addr_val]);;
          `next: val      <- (ccallU "load"  [addr_next]);;
          `_: val         <- (ccallU "free"  [addr_val]);;
          `_: val         <- (ccallU "free"  [addr_next]);;
          `_: val         <- (ccallU "store" [Vptr stk 0; next]);;
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
  (*   return () *)

  Definition pushF: list val -> itree Es val :=
    fun args =>
      '(stk, v)      <- (pargs [Tblk; Tuntyped] args)?;;
      `new_node: val <- (ccallU "alloc" [Vint 2]);;
      let addr_val   := new_node in
      assume(match addr_val with | Vptr _ 0 => True | _ => False end);;;
      addr_next      <- (vadd new_node (Vint 8))?;;
      `hd: val       <- (ccallU "load"  [Vptr stk 0]);;
      `_: val        <- (ccallU "store" [addr_val;   v]);;
      `_: val        <- (ccallU "store" [addr_next; hd]);;
      `_: val        <- (ccallU "store" [Vptr stk 0; new_node]);;
      Ret Vundef
  .

  Definition StackSem: ModSem.t := {|
    ModSem.fnsems := [("new", cfunU newF); ("pop", cfunU popF); ("push", cfunU pushF)];
    ModSem.mn := "Stack";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Stack: Mod.t := {|
    Mod.get_modsem := fun _ => StackSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
