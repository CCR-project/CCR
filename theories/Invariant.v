Require Import Coqlib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import ProofMode.
Require Import SimModSem HTactics.
Require Import STB.

Set Implicit Arguments.







Section AUX.
  Definition invRA: URA.t := Excl.t unit.

  Definition inv_token: (@URA.car invRA) := Some tt.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.

  Definition inv_closed: iProp := OwnM inv_token%I.

  Lemma inv_closed_unique
    :
      inv_closed -∗ inv_closed -∗ False
  .
  Proof.
    unfold inv_closed, inv_token.
    iIntros "H0 H1".
    iCombine "H0 H1" as "H". iOwnWf "H" as WF. exfalso.
    repeat ur in WF. ss.
  Qed.

  Definition inv_le
             A (le: A -> A -> Prop)
    :
      (A + Any.t * Any.t) -> (A + Any.t * Any.t) -> Prop :=
    fun x0 x1 =>
      match x0, x1 with
      | inl a0, inl a1 => le a0 a1
      | inr st0, inr st1 => st0 = st1
      | _, _ => False
      end.

  Lemma inv_le_PreOrder A (le: A -> A -> Prop)
        (PREORDER: PreOrder le)
    :
      PreOrder (inv_le le).
  Proof.
    econs.
    { ii. destruct x; ss. refl. }
    { ii. destruct x, y, z; ss.
      { etrans; et. }
      { subst. auto. }
    }
  Qed.

  Definition inv_wf
             A
             (R: A -> Any.t -> Any.t -> iProp)
    : _ -> (Any.t * Any.t -> Prop) :=
    @mk_wf
      _
      (A + Any.t * Any.t)
      (fun a' mp_src mp_tgt =>
         match a' with
         | inl a => R a mp_src mp_tgt
         | inr (mp_src1, mp_tgt1) => inv_closed ** ⌜mp_src1 = mp_src /\ mp_tgt1 = mp_tgt⌝
         end)%I
  .

  Definition mk_fspec_inv (fsp: fspec): fspec :=
    @mk_fspec
      _
      (meta fsp)
      (fun mn x varg_src varg_tgt o =>
         inv_closed ** (precond fsp) mn x varg_src varg_tgt o)
      (fun mn x vret_src vret_tgt =>
         inv_closed ** (postcond fsp) mn x vret_src vret_tgt).

  Lemma fspec_weaker_fspec_inv_weakker (fsp0 fsp1: fspec)
        (WEAKER: fspec_weaker fsp0 fsp1)
    :
      fspec_weaker (mk_fspec_inv fsp0) (mk_fspec_inv fsp1).
  Proof.
    ii. exploit WEAKER. i. des. exists x_tgt. split; ss.
    { ii. iIntros "[INV H]". iSplitL "INV"; ss.
      iApply PRE. iExact "H". }
    { ii. iIntros "[INV H]". iSplitL "INV"; ss.
      iApply POST. iExact "H". }
  Qed.

End AUX.

Ltac iarg :=
  let PRE := constr:("PRE") in
  let INV := constr:("INV") in
  let CLOSED := constr:("☃CLOSED") in
  eapply (@harg_clo _ _ _ PRE INV);
  [eassumption
  |
  ];
  i;
  mDesSep PRE as CLOSED PRE;
  match goal with
  | [ |- (gpaco7 _ _ _ _ _ _ _ _ ?w _ _)] =>
    destruct w as [?|[?mp_src ?mp_tgt]]; simpl;
    [
        |mAssertPure False; ss; iDestruct "INV" as "[INV _]"; iApply (inv_closed_unique with "☃CLOSED INV")
    ]
  end.

Tactic Notation "icall_open" uconstr(o) uconstr(x) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := constr:("☃CLOSED") in
  let Hns := select_ihyps Hns in
  let Hns := constr:("☃CLOSED"::Hns) in
  eapply (@hcall_clo _ _ Hns POST INV o _ x _ (inr (_, _)));
  unshelve_goal;
  [eassumption
  |start_ipm_proof; iSplitL "☃CLOSED"; [iModIntro; iSplitL "☃CLOSED"; [iExact "☃CLOSED"|ss]|]
  |eauto with ord_step
  |
  |
  on_current ltac:(fun H => try clear H);
  intros ? ? ? ? [|[?mp_src ?mp_tgt]]; i; simpl;
  on_current ltac:(fun H => simpl in H);
  [exfalso; match goal with | H: inv_le _ _ _ |- _ => cbn in H; inv H end
  |mDesSep "☃CLOSED" as "☃CLOSED" "☃TMP"; mPure "☃TMP" as [[] []]
  ]
  ].

Tactic Notation "icall_weaken" uconstr(ftsp) uconstr(o) uconstr(x) uconstr(a) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := get_fresh_name_tac "INV" in
  let CLOSED := constr:("☃CLOSED") in
  let TMP := constr:("☃TMP") in
  let Hns := select_ihyps Hns in
  let Hns := constr:("☃CLOSED"::Hns) in
  eapply (@hcall_clo_weaken _ _ Hns POST INV ftsp o x _ (inl a));
  unshelve_goal;
  [|eassumption
   |start_ipm_proof; iFrame "☃CLOSED"
   |eauto with ord_step
   |
   |on_current ltac:(fun H => try clear H);
    intros ? ? ? ? [|[?mp_src ?mp_tgt]]; i; simpl;
    on_current ltac:(fun H => simpl in H);
    [
      mDesSep POST as "☃CLOSED" POST
    |
    mDesSep INV as "☃CLOSED" INV;
    mDesSep POST as "☃TMP" POST;
    mAssertPure False; [iApply (inv_closed_unique with "☃TMP ☃CLOSED")|ss]
    ]
  ].

Tactic Notation "iret" uconstr(a) :=
  eapply (@hret_clo _ _ _ (inl a)); unshelve_goal;
  [eauto with ord_step
  |eassumption
  |
  |start_ipm_proof; iFrame "☃CLOSED"
  |try by (i; (try unfold lift_rel); esplits; et)
  ].
