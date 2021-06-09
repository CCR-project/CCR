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















Module Ag.
Section Ag.

Context {X: Type}.

Variant car: Type := | bag (P: X -> Prop).

Let _add := fun '(bag xs0) '(bag xs1) => bag (xs0 \1/ xs1).
Let _wf := fun '(bag xs0) => forall x0 x1 (IN0: xs0 x0) (IN1: xs0 x1), x0 = x1.

Program Instance t: URA.t := {
  URA.car := car;
  URA._add := _add;
  URA._wf := _wf;
  URA.unit := (bag bot1);
}
.
Next Obligation.
  unfold _wf, _add in *. i. des_ifs. f_equal. extensionality x. eapply Axioms.prop_ext. tauto.
Qed.
Next Obligation.
  unfold _wf, _add in *. i. des_ifs. f_equal. extensionality x. eapply Axioms.prop_ext. tauto.
Qed.
Next Obligation.
  unfold _wf, _add in *. i. unseal "ra". des_ifs. f_equal. extensionality x. eapply Axioms.prop_ext.
  split; i; des; ss; et.
Qed.
Next Obligation. unfold _wf, _add in *. i. unseal "ra". des_ifs. Qed.
Next Obligation. unfold _wf, _add in *. i. unseal "ra". des_ifs. i. eapply H; et. Qed.

Definition ag (x: X): t := bag (fun x0 => x0 = x).

Theorem duplicable_aux
        ag0
  :
    <<UPD: URA.updatable ag0 (ag0 ⋅ ag0)>>
.
Proof.
  rr. unfold URA.wf, URA.add in *. unseal "ra". ss. ii. r in H. r. des_ifs.
  unfold _add in *. des_ifs.
  i. eapply H; tauto.
Qed.

Theorem duplicable
        x
  :
    <<UPD: URA.updatable (ag x) ((ag x) ⋅ (ag x))>>
.
Proof. eapply duplicable_aux. Qed.

Theorem wf
        x
  :
    <<UPD: URA.wf (ag x)>>
.
Proof. ur. ii. subst. refl. Qed.

Theorem agree
        x y
        (WF: URA.wf ((ag x) ⋅ (ag y)))
  :
    x = y
.
Proof. ur in WF. eapply WF; et. Qed.

End Ag.
End Ag.

Arguments Ag.t: clear implicits.


(* Module Ag. *)
(* Section Ag. *)

(* Context `{X: Type}. *)

(* (* Inductive car: Type := *) *)
(* (* | just (x: list X) *) *)
(* (* | unit *) *)
(* (* | boom *) *)
(* (* . *) *)

(* Let _wf := fun (xs: list X) => forall x0 x1 (IN0: In x0 xs) (IN1: In x1 xs), x0 = x1. *)

(* Program Instance t: URA.t := { *)
(*   URA.car := list X; *)
(*   URA._add := app; *)
(*   URA._wf := _wf; *)
(*   URA.unit := nil; *)
(* } *)
(* . *)
(* Next Obligation. *)
(* Abort. *)

(*** just/unit/boom --> need Dec ***)
(*** list A (just like Iris) --> need equiv class but we don't have ***)








Definition _stkRA: URA.t := (mblock ==> (Ag.t (Z -> Prop)))%ra.
Instance stkRA: URA.t := Auth.t _stkRA.

Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Compute (URA.car (t:=_stkRA)).
  Definition _is_stack (h: mblock) (P: Z -> Prop): _stkRA :=
    (fun _h => if (dec _h h) then (Ag.ag P) else ε)
  .

  Definition is_stack (h: mblock) (P: Z -> Prop): stkRA := Auth.white (_is_stack h P).

  Definition new_spec: fspec :=
    (mk_simple (X:=Z -> Prop)
               (fun P => (
                    (fun varg o => (⌜varg = ([]: list val)↑ /\ o = ord_pure 0⌝: iProp)%I),
                    (fun vret => (∃ h, ⌜vret = (Vptr h 0)↑⌝ ** OwnM (is_stack h P): iProp)%I)
    ))).

  (*** varg stands for (physical) value arguments... bad naming and will be changed later ***)
  Definition pop_spec: fspec :=
    (* (X:=(mblock * list Z)) (AA:=list Z) (AR:=Z * list Z) *)
    mk (fun '(h, P) virtual_arg varg o =>
          (⌜P = virtual_arg /\ varg = ([Vptr h 0%Z]: list val)↑ /\ o = ord_top⌝
            ** OwnM (is_stack h P): iProp)%I)
       (fun '(h, P) '(x, virtual_ret) vret =>
          (((OwnM (is_stack h P) ** ⌜virtual_ret = P ∧ (x = (- 1)%Z ∨ P x)⌝): iProp)%I))
  .

  Definition push_spec: fspec :=
    mk (fun '(h, x, P) virtual_arg varg o =>
          (⌜(x, P) = virtual_arg ∧ varg = ([Vptr h 0%Z; Vint x]: list val)↑ ∧ P x ∧ o = ord_top⌝
            ** OwnM (is_stack h P): iProp)%I)
       (fun '(h, x, P) virtual_ret vret => (⌜virtual_ret = P⌝ ** OwnM (is_stack h P): iProp)%I)
  .

  Definition StackSbtb: list (gname * fspecbody) :=
    [("new", mk_specbody new_spec (fun _ => APC;;; trigger (Choose _)));
    ("pop",  mk_specbody pop_spec (fun (P: Z -> Prop) =>
                                     APC;;;
                                        b <- trigger (Choose _);;
                                     if b: bool
                                     then x <- trigger (Choose _);;
                                          guarantee(P x);;;
                                          trigger (hCall false "debug" [Vint 0; Vint x]↑);;;
                                          Ret (x, P)
                                     else Ret ((- 1)%Z, P)
                                  ));
    ("push", mk_specbody push_spec (fun '(x, P) =>
                                      APC;;;
                                      guarantee(P x);;;
                                      trigger (hCall false "debug" [Vint 1; Vint x]↑);;;
                                      Ret P))
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
