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















Module Ag.
Section Ag.

Context {X: Type}.

Variant car: Type := | bag (P: X -> Prop).
(*** We follow Iris style ***)
(*** - just/unit/boom --> need Dec or excluded_middle_informative ***)
(*** - list A (just like Iris) --> need equiv class but we don't have ***)

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

(*** duplicable **)
(* Theorem dup_aux *)
(*         ag0 *)
(*   : *)
(*     <<UPD: URA.updatable ag0 (ag0 ⋅ ag0)>> *)
(* . *)
(* Proof. *)
(*   rr. unfold URA.wf, URA.add in *. unseal "ra". ss. ii. r in H. r. des_ifs. *)
(*   unfold _add in *. des_ifs. *)
(*   i. eapply H; tauto. *)
(* Qed. *)

Theorem dup_aux
        ag0
        (WF: URA.wf ag0)
  :
    <<UPD: ag0 = (ag0 ⋅ ag0)>>
.
Proof.
  rr. unfold URA.wf, URA.add in *. unseal "ra". ss. destruct ag0. ss. f_equal. extensionality x.
  eapply Axioms.prop_ext. tauto.
Qed.

(* Theorem dup *)
(*         x *)
(*   : *)
(*     <<UPD: URA.updatable (ag x) ((ag x) ⋅ (ag x))>> *)
(* . *)
(* Proof. eapply dup_aux. Qed. *)

Theorem wf
        x
  :
    <<UPD: URA.wf (ag x)>>
.
Proof. ur. ii. subst. refl. Qed.

Theorem dup
        x
  :
    <<UPD: (ag x) = ((ag x) ⋅ (ag x))>>
.
Proof. eapply dup_aux. eapply wf. Qed.

Theorem agree
        x y
        (WF: URA.wf ((ag x) ⋅ (ag y)))
  :
    x = y
.
Proof. ur in WF. eapply WF; et. Qed.

Theorem extends
        x y
        (WF: URA.wf y)
        (EXT: URA.extends (ag x) y)
  :
    y = ag x
.
Proof.
  ur in WF. r in EXT. des; clarify. ur. ur in WF. des_ifs; ss. unfold ag. f_equal.
  extensionality x0. apply Axioms.prop_ext. split; i; et.
Qed.

Lemma ag_inj
      (x0 x1: X)
      (EQ: ag x0 = ag x1)
  :
    x0 = x1
.
Proof.
  clarify. eapply func_ext_rev with (a:=x0) in H0. eapply prop_ext_rev in H0. des; et.
Qed.

End Ag.
End Ag.

Arguments Ag.t: clear implicits.





Module Opt.
Section Opt.

Context {M: URA.t}.

Let _add := fun (x y: option M) => match x, y with
                                   | Some x, Some y => Some (x ⋅ y)
                                   | Some x, _ => Some x
                                   | _, Some y => Some y
                                   | _, _ => None
                                   end.
Let _wf := fun (x: option M) => match x with | Some x => URA.wf x | _ => True end.

Program Instance t: URA.t := {
  URA.car := option M;
  URA._add := _add;
  URA._wf := _wf;
  URA.unit := None;
}
.
Next Obligation.
  unfold _wf, _add in *. i. des_ifs. f_equal. rewrite URA.add_comm. ss.
Qed.
Next Obligation.
  unfold _wf, _add in *. i. des_ifs. f_equal. rewrite URA.add_assoc. ss.
Qed.
Next Obligation. unfold _wf, _add in *. i. unseal "ra". des_ifs. Qed.
Next Obligation. unfold _wf, _add in *. i. unseal "ra". des_ifs. Qed.
Next Obligation. unfold _wf, _add in *. i. unseal "ra". des_ifs. eapply URA.wf_mon; et. Qed.

Theorem wf
        m
  :
    (<<WF: URA.wf (Some m)>>) <-> <<WF: URA.wf m>>
.
Proof.
  split; i.
  - ur in H; ss.
  - ur; ss.
Qed.

Theorem extends
        x0 m
        (WF: URA.wf m)
        (EXT: URA.extends (Some x0) m)
  :
    exists x1, m = Some x1 ∧ <<EXT: URA.extends x0 x1>>
.
Proof.
  r in EXT. des; clarify. ur. ss. ur in WF. des_ifs; ss.
  - esplits; et. r. esplits; et.
  - esplits; et. refl.
Qed.

End Opt.
End Opt.

Arguments Opt.t: clear implicits.







Module Ag2.
Section Ag2.

Context {X: Type}.

Variant car: Type := ag (x: X) | unit | boom.

Let _add := fun x y => match x, y with
                       | ag x, ag y => if excluded_middle_informative (x = y) then ag x else boom
                       | _, unit => x | unit, _ => y | _, _ => boom
                       end.
Let _wf := fun a => a <> boom.

Program Instance t: URA.t := {
  URA.car := car;
  URA._add := _add;
  URA._wf := _wf;
  URA.unit := unit;
}
.
Next Obligation.
  unfold _wf, _add in *. i. des_ifs.
Qed.
Next Obligation.
  unfold _wf, _add in *. i. des_ifs.
Qed.
Next Obligation.
  unfold _wf, _add in *. i. unseal "ra". des_ifs.
Qed.
Next Obligation. unfold _wf, _add in *. i. unseal "ra". des_ifs. Qed.
Next Obligation. unfold _wf, _add in *. i. unseal "ra". des_ifs. Qed.

(* Definition ag (x: X): t := just x. *)

(*** duplicable **)
(* Theorem dup_aux *)
(*         ag0 *)
(*   : *)
(*     <<UPD: URA.updatable ag0 (ag0 ⋅ ag0)>> *)
(* . *)
(* Proof. *)
(*   rr. unfold URA.wf, URA.add in *. unseal "ra". ss. ii. r in H. r. des_ifs. *)
(*   unfold _add in *. des_ifs. *)
(*   i. eapply H; tauto. *)
(* Qed. *)

Theorem dup_aux
        ag0
        (WF: URA.wf ag0)
  :
    <<UPD: ag0 = (ag0 ⋅ ag0)>>
.
Proof. rr. unfold URA.wf, URA.add in *. unseal "ra". ss. destruct ag0; ss. des_ifs. Qed.

(* Theorem dup *)
(*         x *)
(*   : *)
(*     <<UPD: URA.updatable (ag x) ((ag x) ⋅ (ag x))>> *)
(* . *)
(* Proof. eapply dup_aux. Qed. *)

Theorem wf
        x
  :
    <<UPD: URA.wf (ag x)>>
.
Proof. ur. ss. Qed.

Theorem dup
        x
  :
    <<UPD: (ag x) = ((ag x) ⋅ (ag x))>>
.
Proof. eapply dup_aux. eapply wf. Qed.

Theorem agree
        x y
        (WF: URA.wf ((ag x) ⋅ (ag y)))
  :
    x = y
.
Proof. ur in WF. des_ifs. Qed.

Theorem extends
        x y
        (WF: URA.wf y)
        (EXT: URA.extends (ag x) y)
  :
    y = ag x
.
Proof. ur in WF. r in EXT. des; clarify. ur. ur in WF. des_ifs; ss. Qed.

End Ag2.
End Ag2.

Arguments Ag2.t: clear implicits.









Definition _stkRA: URA.t := (mblock ==> (Opt.t (Ag.t (Z -> Prop))))%ra.
Instance stkRA: URA.t := Auth.t _stkRA.

Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Compute (URA.car (t:=_stkRA)).
  Definition _is_stack (h: mblock) (P: Z -> Prop): _stkRA :=
    (fun _h => if (dec _h h) then Some (Ag.ag P) else ε)
  .

  Definition is_stack (h: mblock) (P: Z -> Prop): stkRA := Auth.white (_is_stack h P).

  Theorem is_stack_dup
          h P
    :
      <<UPD: URA.updatable (is_stack h P) ((is_stack h P) ⋅ (is_stack h P))>>
  .
  Proof.
    unfold is_stack. eapply Auth.auth_dup_white. unfold _is_stack.
    extensionality _h. ss. ur. des_ifs.
    - ur. erewrite <- Ag.dup; ss.
    - ur. ss.
  Qed.

  Definition new_spec: fspec :=
    (mk_simple (fun P => (
                    (fun varg o => (⌜varg = (Any.pair tt↑ ([]: list val)↑) /\ o = ord_pure 0⌝: iProp)%I),
                    (fun vret => (∃ h, ⌜vret = (Vptr h 0)↑⌝ ** OwnM (is_stack h P): iProp)%I)
    ))).

  Definition pop_spec: fspec :=
    mk_simple (fun '(h, P) => (
                 (fun varg o => (⌜varg = (Any.pair tt↑ ([Vptr h 0%Z]: list val)↑) /\ o = ord_pure 1⌝
                                  ** OwnM (is_stack h P): iProp)%I),
                 (fun vret =>
                    (((OwnM (is_stack h P) ** ∃ x, ⌜(x = (- 1)%Z ∨ P x) ∧ vret = (Vint x)↑⌝): iProp)%I))
              ))
  .

  Definition push_spec: fspec :=
    mk_simple (fun '(h, P) => (
                   (fun varg o => (OwnM (is_stack h P)
                        ** ∃ x, ⌜varg = (Any.pair tt↑ ([Vptr h 0%Z; Vint x]: list val)↑) ∧ P x ∧ o = ord_pure 1⌝: iProp)%I),
                   (fun vret => (((OwnM (is_stack h P)): iProp)%I))
              ))
  .

  Definition StackSbtb: list (gname * fspecbody) :=
    [("new", mk_specbody new_spec (fun _ => trigger (Choose _)));
    ("pop",  mk_specbody pop_spec (fun _ => trigger (Choose _)));
    ("push", mk_specbody push_spec (fun _ => trigger (Choose _)))
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
