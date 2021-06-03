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

Set Implicit Arguments.





Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Fixpoint is_list (ll: val) (xs: list val): iProp :=
    match xs with
    | [] => (⌜ll = Vnullptr⌝: iProp)%I
    | xhd :: xtl =>
      (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl]))
                             ** is_list ltl xtl: iProp)%I
    end
  .

  Definition pop_spec: ftspec unit unit :=
    (mk_ksimple (fun '(llref, xs) => (
                     (fun varg o =>
                        (∃ ll, ⌜varg = [Vptr llref 0%Z]↑⌝ ** OwnM ((llref,0%Z) |-> [ll])
                                                       ** (is_list ll xs) ** ⌜o = ord_pure 2⌝: iProp)%I),
                     (fun vret =>
                        (match xs with
                         | [] => ⌜vret = (Vint (- 1))↑⌝
                         | xhd :: xtl => ⌜vret = xhd↑⌝ ** (∃ ll', OwnM ((llref,0%Z) |-> [ll']) ** is_list ll' xtl)
                         end: iProp)%I)
    ))).

  Definition push_spec: ftspec unit unit :=
    (mk_ksimple (fun '(x, xs) => (
                     (fun varg o => (∃ ll, ⌜varg = [ll; x]↑⌝ ** is_list ll xs ** ⌜o = ord_pure 2⌝)%I),
                     (fun vret => (∃ ll', is_list ll' (x :: xs) ** ⌜vret = ll'↑⌝)%I)
    ))).

  Definition StackSbtb: list (gname * kspecbody) :=
    [("pop", mk_kspecbody pop_spec
                          (fun args => trigger (kCall "debug" (inr args));;; APCK;;; trigger (Choose _)));
    ("push",   mk_kspecbody push_spec (fun _ => APCK;;; trigger (Choose _)))
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
    KModSem.initial_st := tt↑;
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
