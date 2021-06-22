Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import ProofMode.
Require Import HTactics.

Set Implicit Arguments.







Section AUX.
  Definition invRA: URA.t := Auth.t (Excl.t unit).

  Definition inv_black: (@URA.car invRA)
    := Auth.black (M:=(Excl.t _)) (Some tt).
  Definition inv_white: (@URA.car invRA)
    := Auth.white (M:=(Excl.t _)) (Some tt).

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.

  Definition inv_closed: iProp := OwnM inv_black%I.
  Definition inv_open: iProp := OwnM inv_white%I.

  Lemma inv_open_unique
    :
      inv_open -∗ inv_open -∗ False
  .
  Proof.
    unfold inv_open, inv_closed, inv_white, inv_black.
    iIntros "H0 H1".
    iCombine "H0 H1" as "H". iOwnWf "H" as WF. exfalso.
    repeat ur in WF. ss.
  Qed.

  Lemma inv_closed_unique
    :
      inv_closed -∗ inv_closed -∗ False
  .
  Proof.
    unfold inv_open, inv_closed, inv_white, inv_black.
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
             (R_src: A -> Any.t -> Any.t -> iProp)
             (R_tgt: A -> Any.t -> Any.t -> iProp)
    : _ -> (((Σ * Any.t)) * ((Σ * Any.t)) -> Prop) :=
    @mk_wf
      _
      (A + Any.t * Any.t)
      (fun a' mp_src mp_tgt =>
         match a' with
         | inl a => inv_closed ** R_src a mp_src mp_tgt
         | inr (mp_src1, mp_tgt1) => inv_open ** ⌜mp_src1 = mp_src /\ mp_tgt1 = mp_tgt⌝
         end)%I
      (fun a' mp_src mp_tgt =>
         match a' with
         | inl a => R_tgt a mp_src mp_tgt
         | inr (mp_src, mp_tgt) => top1
         end)
  .

  Definition mk_inv_simple {X: Type} (PQ: X -> ((Any.t -> ord -> iProp) * (Any.t -> iProp))): fspec :=
    mk_simple
      (fun (x: X) =>
         ((fun varg o =>
             inv_open
               **
               (fst (PQ x) varg o)),
          (fun vret =>
             inv_open
               **
               (snd (PQ x) vret)))
      ).
End AUX.

Ltac iarg :=
  let PRE := constr:("PRE") in
  let INV := constr:("INV") in
  let OPENER := constr:("☃OPENER") in
  let CLOSED := constr:("☃CLOSED") in
  let TMP := constr:("☃TMP") in
  let ARG := constr:("ARG") in
  eapply (@harg_clo _ _ _ PRE INV);
  [eassumption
  |
  ];
  i;
  let aa := fresh "aa" in
  mDesAndPureR PRE as PRE ARG;
  let EQ := fresh "EQ" in
  mPure ARG as EQ;
  try (destruct EQ);
  mDesSep PRE as OPENER PRE;
  match goal with
  | [ |- (gpaco7 _ _ _ _ _ _ _ _ ?w _ _)] =>
    destruct w as [?|[?mp_src ?mp_tgt]]; simpl;
    [mDesSep INV as CLOSED INV
    |mAssertPure False; ss; iDestruct "INV" as "[INV _]"; iApply (inv_open_unique with "☃OPENER INV")
    ]
  end.

Tactic Notation "icall_open" uconstr(o) uconstr(x) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := constr:("☃OPENER") in
  let Hns := select_ihyps Hns in
  let Hns := constr:("☃OPENER"::Hns) in
  eapply (@hcall_clo _ _ Hns POST INV o _ x _ (inr (_, _)));
  unshelve_goal;
  [eassumption
  |
  |start_ipm_proof; iSplitL "☃OPENER"; [iModIntro; iFrame; ss|]
  |eauto with ord_step
  |
  |on_current ltac:(fun H => try clear H);
   intros ? ? ? ? ? ? [|[?mp_src ?mp_tgt]]; i; simpl;
   on_current ltac:(fun H => simpl in H);
   [mDesSep "☃OPENER" as "☃OPENER" "☃TMP";
    mAssertPure False; ss; iApply (inv_closed_unique with "☃OPENER ☃CLOSED")
   |mDesSep "☃OPENER" as "☃OPENER" "☃TMP"; mPure "☃TMP" as [[] []]
   ]
  ].

Tactic Notation "icall_weaken" uconstr(ftsp) uconstr(o) uconstr(x) uconstr(a) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := get_fresh_name_tac "INV" in
  let CLOSED := constr:("☃CLOSED") in
  let TMP := constr:("☃TMP") in
  let OPENER := constr:("☃OPENER") in
  let Hns := select_ihyps Hns in
  let Hns := constr:("☃CLOSED"::"☃OPENER"::Hns) in
  eapply (@hcall_clo_weaken _ _ Hns POST INV ftsp o x _ (inl a));
  unshelve_goal;
  [|
   eassumption
   |
   |start_ipm_proof
    ; iFrame "☃CLOSED ☃OPENER"
   |eauto with ord_step
   |
   |on_current ltac:(fun H => try clear H);
    intros ? ? ? ? ? ? [|[?mp_src ?mp_tgt]]; i; simpl;
    on_current ltac:(fun H => simpl in H);
    [mDesSep INV as "☃CLOSED" INV;
     mDesAndPureR POST as POST "☃TMP";
     let EQ := fresh "EQ" in
     mPure "☃TMP" as EQ; try (symmetry in EQ; destruct EQ);
     mDesSep POST as "☃OPENER" POST
    |mDesSep INV as "☃CLOSED" INV;
     mDesAndPureR POST as POST "☃TMP";
     mDesSep POST as "☃OPENER" POST;
     mAssertPure False; [iApply (inv_open_unique with "☃OPENER ☃CLOSED")|ss]
    ]
  ].

Tactic Notation "iret" uconstr(a) :=
  eapply (@hret_clo _ _ _ (inl a)); unshelve_goal;
  [eauto with ord_step
  |eassumption
  |
  |
  |start_ipm_proof; iFrame "☃CLOSED ☃OPENER"
  |
  ].



Definition knotRA: URA.t := Auth.t (Excl.t (option (nat -> nat))).
Definition knot_full (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.black (M:=(Excl.t _)) (Some f).
Definition knot_frag (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.white (M:=(Excl.t _)) (Some f).

Definition knot_init: (@URA.car knotRA) := knot_frag None.

Section REC.
  Context `{Σ: GRA.t}.

  Definition mrec_spec (f: nat -> nat) (INV: iProp): fspec :=
    mk_simple (X:=nat)
              (fun n => (
                   (fun varg o =>
                      (⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure (2 * n + 1)%nat⌝)
                        ** INV
                   ),
                   (fun vret =>
                      (⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                        ** INV
                   )
              )).

End REC.
