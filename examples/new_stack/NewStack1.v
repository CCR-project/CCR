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
Require Import TODOYJ.
Require Import AList.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Notation pget := (p0 <- trigger PGet;; `p0: (gmap mblock (list Z)) <- p0↓ǃ;; Ret p0) (only parsing).
  Notation pput p0 := (trigger (PPut (p0: (gmap mblock (list Z)))↑)) (only parsing).

  (* def new(): Ptr *)
  (*   let handle := Choose(Ptr); *)
  (*   guarantee(stk_mgr(handle) = None); *)
  (*   stk_mgr(handle) := Some []; *)
  (*   return handle *)

  Definition new_body: list val -> itree (kCallE +' pE +' eventE) val :=
    fun args =>
      _ <- (pargs [] args)?;;
      APCK;;;
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
  (*     return x *)
  (*   | [] => return -1 *)
  (*   end *)

  Definition pop_body: list val -> itree (kCallE +' pE +' eventE) val :=
    fun args =>
      handle <- (pargs [Tblk] args)?;;
      stk_mgr0 <- pget;;
      stk0 <- (stk_mgr0 !! handle)?;;
      let stk_mgr1 := delete handle stk_mgr0 in pput stk_mgr1;;;
      APCK;;;
      match stk0 with
      | x :: stk1 =>
        stk_mgr2 <- pget;; pput (<[handle:=stk1]> stk_mgr2);;;
        Ret (Vint x)
      | _ =>
        stk_mgr2 <- pget;; pput (<[handle:=[]]> stk_mgr2);;;
        Ret (Vint (- 1))
      end
  .

  (* def push(handle: Ptr, x: Int64): Unit *)
  (*   let stk := unwrap(stk_mgr(handle)); *)
  (*   stk_mgr(handle) := Some (x :: stk); *)
  (*   () *)

  Definition push_body: list val -> itree (kCallE +' pE +' eventE) val :=
    fun args =>
      '(handle, x) <- (pargs [Tblk; Tint] args)?;;
      stk_mgr0 <- pget;;
      stk0 <- (stk_mgr0 !! handle)?;;
      let stk_mgr1 := delete handle stk_mgr0 in pput stk_mgr1;;;
      APCK;;;
      stk_mgr2 <- pget;; pput (<[handle:=(x :: stk0)]> stk_mgr2);;;
      Ret Vundef
  .

  Definition StackSbtb: list (gname * kspecbody) :=
    [("new", ksb_trivial (cfun new_body));
    ("pop", ksb_trivial (cfun pop_body));
    ("push", ksb_trivial (cfun push_body))
    ].

  Definition StackStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun ksb => (KModSem.disclose_ksb ksb): fspec)) StackSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition KStackSem: KModSem.t := {|
    KModSem.fnsems := StackSbtb;
    KModSem.mn := "Stack";
    KModSem.initial_mr := ε;
    KModSem.initial_st := (∅: gmap mblock (list Z))↑;
  |}
  .
  Definition SStackSem: SModSem.t := KStackSem.
  Definition StackSem (stb: list (string * fspec)): ModSem.t :=
    (SModSem.to_tgt stb) SStackSem.



  Definition KStack: KMod.t := {|
    KMod.get_modsem := fun _ => KStackSem;
    KMod.sk := Sk.unit;
  |}
  .
  Definition SStack: SMod.t := KStack.
  Definition Stack (stb: Sk.t -> list (string * fspec)): Mod.t :=
    SMod.to_tgt stb SStack.

End PROOF.
Global Hint Unfold StackStb: stb.
