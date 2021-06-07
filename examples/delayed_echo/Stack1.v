Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Logic.
Require Import Mem1.
Require Import TODOYJ.

Set Implicit Arguments.





Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Let pop_spec: fspec := (mk_simple (fun '(llref, xs) => (
                                         (fun varg o =>
                                            (∃ ll, ⌜varg = [Vptr llref 0%Z]↑⌝ ** OwnM ((llref,0%Z) |-> [ll])
                                                                           ** (is_list ll xs) ** ⌜o = ord_pure 2⌝: iProp)%I),
                                         (fun vret =>
                                            (match xs with
                                             | [] => ⌜vret = (Vint (- 1))↑⌝
                                             | xhd :: xtl => ⌜vret = xhd↑⌝ ** (∃ ll', OwnM ((llref,0%Z) |-> [ll']) ** is_list ll' xtl)
                                             end: iProp)%I)
                         ))).

  Let pop2_spec: fspec := (mk_simple (fun '(xs, nref) => (
                                          (fun varg o => (∃ ll, ⌜varg = [ll; Vptr nref 0%Z]↑⌝ ** (is_list ll xs) **
                                                                                           (∃ v, OwnM ((nref, 0%Z) |-> [v])) **
                                                                                           ⌜o = ord_pure 2⌝)%I),
                                          (fun vret =>
                                             (match xs with
                                              | [] => ⌜vret = Vnullptr↑⌝
                                              | xhd :: xtl => ∃ ll', ⌜vret = ll'↑⌝ ** is_list ll' xtl **
                                                                                OwnM ((nref, 0%Z) |-> [xhd])
                                              end)%I)
                          ))).

(* struct Node* pop2(struct Node* ll, int *n) { *)
(*   if(ll) { *)
(*     int v = (ll)->val; *)
(*     struct Node* next = (ll)->next; *)
(*     free(ll); *)
(*     *n = v; *)
(*     return next; *)
(*   } *)
(*   return NULL; *)
(* } *)

  Let push_spec: fspec := (mk_simple (fun '(x, xs) => (
                                          (fun varg o => (∃ ll, ⌜varg = [ll; x]↑⌝ ** is_list ll xs ** ⌜o = ord_pure 2⌝)%I),
                                          (fun vret => (∃ ll', is_list ll' (x :: xs) ** ⌜vret = ll'↑⌝)%I)
                          ))).

  Definition StackStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("pop", pop_spec) ; ("pop2", pop2_spec) ; ("push", push_spec)].
  Defined.

  Definition StackSbtb: list (gname * fspecbody) :=
    [("pop", mk_specbody pop_spec (fun _ => APC;;; trigger (Choose _)));
    ("pop2", mk_specbody pop2_spec (fun _ => APC;;; trigger (Choose _)));
    ("push",   mk_specbody push_spec (fun _ => APC;;; trigger (Choose _)))
    ]
  .

  Definition SStackSem: SModSem.t := {|
    SModSem.fnsems := StackSbtb;
    SModSem.mn := "Stack";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition StackSem: ModSem.t := (SModSem.to_tgt (MemStb ++ StackStb)) SStackSem.

  Definition SStack: SMod.t := {|
    SMod.get_modsem := fun _ => SStackSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition Stack: Mod.t := (SMod.to_tgt (fun _ => MemStb ++ StackStb)) SStack.

End PROOF.
Global Hint Unfold StackStb: stb.
