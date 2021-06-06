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



(*** TODO: replace the one in AList.v ***)
Global Instance function_Map `{Dec K} V: (Map K V (K -> option V)) :=
  Build_Map
    (fun _ => None)
    (fun k0 v m => fun k1 => if dec k0 k1 then Some v else m k1)
    (fun k0 m => fun k1 => if dec k0 k1 then None else m k1)
    (fun k m => m k)
    (fun m0 m1 => fun k => match (m0 k) with
                           | Some v => Some v
                           | _ => m1 k
                           end).

Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  (*** TODO: move to OpenDef; align it with trivial_fspec2 ***)
  Definition trivial_bottom_spec: ftspec unit unit :=
    (mk_ksimple (fun (_: unit) => ((fun _ _ => (⌜False⌝: iProp)%I),
                                   (fun _ => (⌜True⌝: iProp)%I))))
  .

  Definition new_spec: ftspec unit unit := trivial_bottom_spec.
  Definition pop_spec: ftspec unit unit := trivial_bottom_spec.
  Definition push_spec: ftspec unit unit := trivial_bottom_spec.

  Notation pget := (p0 <- trigger PGet;; `p0: (gmap mblock (list Z)) <- p0↓ǃ;; Ret p0) (only parsing).
  Notation pput p0 := (trigger (PPut p0↑)) (only parsing).

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
  (*     debug(false, x); *)
  (*     return x *)
  (*   | [] => return -1 *)
  (*   end *)

  Definition pop_body: list val -> itree (kCallE +' pE +' eventE) val :=
    fun args =>
      handle <- (pargs [Tblk] args)?;;
      stk_mgr0 <- pget;;
      stk0 <- (stk_mgr0 !! handle)?;;
      APCK;;;
      match stk0 with
      | x :: stk1 =>
        pput (<[handle:=stk1]> stk_mgr0);;;
        trigger (kCall "debug" (inr [Vint 0; Vint x]));;;
        Ret (Vint x)
      | _ => Ret (Vint (- 1))
      end
  .

  (* def push(handle: Ptr, x: Int64): Unit *)
  (*   let stk := unwrap(stk_mgr(handle)); *)
  (*   stk_mgr(handle) := Some (x :: stk); *)
  (*   debug(true, x); *)
  (*   () *)

  Definition push_body: list val -> itree (kCallE +' pE +' eventE) val :=
    fun args =>
      '(handle, x) <- (pargs [Tblk; Tint] args)?;;
      stk_mgr0 <- pget;;
      APCK;;;
      stk0 <- (stk_mgr0 !! handle)?;;
      pput (<[handle:=(x :: stk0)]> stk_mgr0);;;
      trigger (kCall "debug" (inr [Vint 1; Vint x]));;;
      Ret Vundef
  .

  Definition StackSbtb: list (gname * kspecbody) :=
    [("new", mk_kspecbody new_spec new_body);
    ("pop", mk_kspecbody pop_spec pop_body);
    ("push",   mk_kspecbody push_spec push_body)
    ].

  Definition StackStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun ksb => (KModSem.disclose_ksb ksb): fspec)) StackSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition DebugStb: list (gname * fspec).
   eapply (Seal.sealing "stb").
   eapply [("debug", fspec_trivial2)].
  Defined.

  Definition KStackSem: KModSem.t := {|
    KModSem.fnsems := StackSbtb;
    KModSem.mn := "Stack";
    KModSem.initial_mr := ε;
    KModSem.initial_st := (gmap_empty: gmap mblock (list Z))↑;
  |}
  .

  Definition SStackSem: SModSem.t := (KModSem.to_tgt) KStackSem.

  Definition StackSem (stb: list (string * fspec)): ModSem.t :=
    (SModSem.to_tgt stb) SStackSem.

  Definition KStack: KMod.t := {|
    KMod.get_modsem := fun _ => KStackSem;
    KMod.sk := Sk.unit;
  |}
  .

  Definition SStack: SMod.t := (KMod.to_tgt) KStack.

  Definition Stack (stb: Sk.t -> list (string * fspec)): Mod.t :=
    SMod.to_tgt stb SStack.

End PROOF.
Global Hint Unfold StackStb: stb.
Global Hint Unfold DebugStb: stb.
