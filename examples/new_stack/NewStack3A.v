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



Definition _stkRA: URA.t := (mblock ==> (Excl.t (list Z)))%ra.
Instance stkRA: URA.t := Auth.t _stkRA.

Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Compute (URA.car (t:=_stkRA)).
  Definition _is_stack (h: mblock) (stk: list Z): _stkRA :=
    (fun _h => if (dec _h h) then Some stk else ε)
  .

  Definition is_stack (h: mblock) (stk: list Z): stkRA := Auth.white (_is_stack h stk).

  Let new_spec: fspec :=
    (mk_simple (X:=unit)
               (fun _ => (
                    (fun varg o => (⌜varg = ([]: list val)↑ /\ o = ord_pure 0⌝: iProp)%I),
                    (fun vret => (∃ h, ⌜vret = (Vptr h 0)↑⌝ ** OwnM (is_stack h []): iProp)%I)
    ))).

  Let pop_spec: fspec :=
    (mk_simple (fun '(h, stk0) => (
                    (fun varg o => (⌜varg = ([Vptr h 0%Z]: list val)↑ /\ o = ord_pure 0⌝ **
                                    OwnM (is_stack h stk0): iProp)%I),
                    (fun vret => (match stk0 with
                                  | [] => ⌜vret = (Vint (- 1))↑⌝ ** OwnM (is_stack h [])
                                  | x :: stk1 => ⌜vret = x↑⌝ ** OwnM (is_stack h stk1)
                                  end: iProp)%I)
    ))).

  Let push_spec: fspec :=
    (mk_simple (fun '(h, x, stk0) => (
                    (fun varg o => (⌜varg = ([Vptr h 0%Z; Vint x]: list val)↑ /\ o = ord_pure 0⌝ **
                                    OwnM (is_stack h stk0): iProp)%I),
                    (fun vret => (OwnM (is_stack h (x :: stk0)): iProp)%I)
    ))).

  Definition StackSbtb: list (gname * fspecbody) :=
    [("new", mk_specbody new_spec (fun _ => APC;;; trigger (Choose _)));
    ("pop",  mk_specbody pop_spec (fun _ => APC;;; trigger (Choose _)));
    ("push", mk_specbody push_spec (fun _ => APC;;; trigger (Choose _)))
    ].

  Definition StackStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd fsb_fspec) StackSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition SStackSem: SModSem.t := {|
    SModSem.fnsems := StackSbtb;
    SModSem.mn := "Stack";
    SModSem.initial_mr := (GRA.embed (Auth.black (M:=_stkRA) (fun _ => ε)));
    SModSem.initial_st := tt↑;
  |}
  .

  Definition StackSem: ModSem.t := (SModSem.to_tgt (StackStb)) SStackSem.

  Definition SStack: SMod.t := {|
    SMod.get_modsem := fun _ => SStackSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition Stack: Mod.t := (SMod.to_tgt (fun _ => StackStb)) SStack.

End PROOF.
Global Hint Unfold StackStb: stb.
