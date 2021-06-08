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
Require Import NewStackHeader.

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

  Definition new_spec: fspec :=
    (mk_simple (X:=unit)
               (fun _ => (
                    (fun varg o => (⌜varg = ([]: list val)↑ /\ o = ord_pure 0⌝: iProp)%I),
                    (fun vret => (∃ h, ⌜vret = (Vptr h 0)↑⌝ ** OwnM (is_stack h []): iProp)%I)
    ))).

  (*** varg stands for (physical) value arguments... bad naming and will be changed later ***)
  Definition pop_spec: fspec :=
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

  Definition StackSbtb: list (gname * fspecbody) :=
    [("new", mk_specbody new_spec (fun _ => APC;;; trigger (Choose _)));
    ("pop",  mk_specbody pop_spec (fun (stk0: list Z) =>
                                     APC;;; match stk0 with
                                            | [] => Ret ((- 1)%Z, [])
                                            | x :: stk1 =>
                                              trigger (hCall false "debug" [Vint 0; Vint x]↑);;; Ret (x, stk1)
                                            end));
    ("push", mk_specbody push_spec (fun '(x, stk0) =>
                                      APC;;; trigger (hCall false "debug" [Vint 1; Vint x]↑);;;
                                         Ret (x :: stk0)))
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

  Definition StackSem (stb: list (string * fspec)): ModSem.t := (SModSem.to_tgt stb) SStackSem.

  Definition SStack: SMod.t := {|
    SMod.get_modsem := fun _ => SStackSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition Stack (stb: Sk.t -> list (string * fspec)): Mod.t := (SMod.to_tgt stb) SStack.

End PROOF.
Global Hint Unfold StackStb: stb.
