Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef OpenDef.
Require Import Logic.
Require Import Mem1.
Require Import TODO TODOYJ.
Require Import AList.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Notation pget := (p0 <- trigger PGet;; `p0: (gmap mblock (list Z)) <- p0↓ǃ;; Ret p0) (only parsing).
  Notation pput p0 := (trigger (PPut p0↑)) (only parsing).

  (* def new(): Ptr *)
  (*   let handle := Choose(Ptr); *)
  (*   guarantee(stk_mgr(handle) = None); *)
  (*   stk_mgr(handle) := Some []; *)
  (*   return handle *)

  Definition new_body: list val -> itree Es val :=
    fun args =>
      _ <- (pargs [] args)?;;
      handle <- trigger (Choose _);;
      stk_mgr0 <- pget;;
      guarantee(stk_mgr0 !! handle = None);;;
      let stk_mgr1 := <[handle:=[]]> stk_mgr0 in
      pput stk_mgr1;;;
      Ret (Vptr handle 0)
  .

  (* def pop(handle: Ptr): Int64 *)
  (*   let stk := unwrap(stk_mgr(handle)); *)
  (*   match stk with *)
  (*   | x :: stk' =>  *)
  (*     stk_mgr(handle) := Some stk'; *)
  (*     debug(false, x); *)
  (*     return x *)
  (*   | [] => return -1 *)
  (*   end *)

  Definition pop_body: list val -> itree Es val :=
    fun args =>
      handle <- (pargs [Tblk] args)?;;
      stk_mgr0 <- pget;;
      stk0 <- (stk_mgr0 !! handle)?;;
      match stk0 with
      | x :: stk1 =>
        pput (<[handle:=stk1]> stk_mgr0);;;
        trigger (Call "debug" ([Vint 0; Vint x])↑);;;
        Ret (Vint x)
      | _ => Ret (Vint (- 1))
      end
  .

  (* def push(handle: Ptr, x: Int64): Unit *)
  (*   let stk := unwrap(stk_mgr(handle)); *)
  (*   stk_mgr(handle) := Some (x :: stk); *)
  (*   debug(true, x); *)
  (*   () *)

  Definition push_body: list val -> itree Es val :=
    fun args =>
      '(handle, x) <- (pargs [Tblk; Tint] args)?;;
      stk_mgr0 <- pget;;
      stk0 <- (stk_mgr0 !! handle)?;;
      pput (<[handle:=(x :: stk0)]> stk_mgr0);;;
      trigger (Call "debug" ([Vint 1; Vint x]↑));;;
      Ret Vundef
  .

  Definition cfun2 X Y (f: X -> itree Es Y): Any.t -> itree Es Any.t :=
    fun args => map_or_else (Any.split args)
                            (fun '(_, args) => args <- unwrapN args↓;; ret <- f args;; Ret (ret↑))
                            (args <- unwrapN args↓;; ret <- f args;; Ret (ret↑))
  .

  Definition StackSem: ModSem.t := {|
    ModSem.fnsems := [("new", cfun2 new_body); ("pop", cfun2 pop_body); ("push", cfun2 push_body)];
    ModSem.mn := "Stack";
    ModSem.initial_mr := ε;
    ModSem.initial_st := (∅: gmap mblock (list Z))↑;
  |}
  .

  Definition Stack: Mod.t := {|
    Mod.get_modsem := fun _ => StackSem;
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.
