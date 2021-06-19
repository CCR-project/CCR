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
Require Import IPM HoareDef OpenDef.

Set Implicit Arguments.




Section PROOF.

  Context `{Σ: GRA.t}.

  Definition echo_spec: fspec :=
    mk_simple (fun (_: unit) => (
                   (fun argh o => (⌜argh = ([]: list val)↑ ∧ o = ord_top⌝)%I),
                   (fun reth => (⌜reth = Vundef↑⌝)%I)
                 ))
  .

  (*** varg stands for (physical) value arguments... bad naming and will be changed later ***)
  Definition input_spec: fspec :=
    (* (X:=(mblock * list Z)) (AA:=list Z) (AR:=Z * list Z) *)
    mk (fun '(h, stk0) virtual_arg varg o =>
          (⌜stk0 = virtual_arg /\ varg = ([Vptr h 0%Z]: list val)↑ /\ o = ord_top⌝
            ** OwnM (is_stack h stk0): iProp)%I)
       (fun '(h, stk0) '(x, stk1) vret =>
          (match stk0 with
           | [] => ⌜x = (- 1)%Z /\ (stk1 = [])⌝ ** OwnM (is_stack h stk1)
           | hd :: tl => ⌜x = hd /\ (stk1 = tl)⌝ ** OwnM (is_stack h stk1)
           end: iProp)%I)
  .

  Definition push_spec: fspec :=
    mk (fun '(h, x, stk0) virtual_arg varg o =>
          (⌜(x, stk0) = virtual_arg /\ varg = ([Vptr h 0%Z; Vint x]: list val)↑ /\ o = ord_top⌝
            ** OwnM (is_stack h stk0): iProp)%I)
       (fun '(h, x, stk0) stk1 vret => (⌜stk1 = x :: stk0⌝ ** OwnM (is_stack h stk1): iProp)%I)
  .


  (*** TODO: remove redundancy with NewStack2 ***)
  Notation pget := (p0 <- trigger PGet;; `p0: (gmap mblock (list Z)) <- p0↓ǃ;; Ret p0) (only parsing).
  Notation pput p0 := (trigger (PPut (p0: (gmap mblock (list Z)))↑)) (only parsing).

  Definition new_body: list val -> itree (kCallE +' pE +' eventE) val :=
    fun args =>
      _ <- (pargs [] args)?;;
      handle <- trigger (Choose _);;
      stk_mgr0 <- pget;;
      guarantee(stk_mgr0 !! handle = None);;;
      let stk_mgr1 := <[handle:=[]]> stk_mgr0 in
      pput stk_mgr1;;;
      Ret (Vptr handle 0)
  .

  Definition pop_body: list val -> itree (kCallE +' pE +' eventE) val :=
    fun args =>
      handle <- (pargs [Tblk] args)?;;
      stk_mgr0 <- pget;;
      stk0 <- (stk_mgr0 !! handle)?;;
      match stk0 with
      | x :: stk1 =>
        pput (<[handle:=stk1]> stk_mgr0);;;
        Ret (Vint x)
      | _ => Ret (Vint (- 1))
      end
  .

  Definition push_body: list val -> itree (kCallE +' pE +' eventE) val :=
    fun args =>
      '(handle, x) <- (pargs [Tblk; Tint] args)?;;
      stk_mgr0 <- pget;;
      stk0 <- (stk_mgr0 !! handle)?;;
      pput (<[handle:=(x :: stk0)]> stk_mgr0);;;
      Ret Vundef
  .


  Definition StackSbtb: list (gname * kspecbody) :=
    [("new", mk_kspecbody new_spec (cfun new_body) (fun _ => trigger (Choose _)));
    ("pop",  mk_kspecbody pop_spec (cfun pop_body) (fun _ => trigger (Choose _)));
    ("push", mk_kspecbody push_spec (cfun push_body) (fun _ => trigger (Choose _)))
    ]
  .

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
