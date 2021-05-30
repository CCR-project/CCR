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
  Definition invRA: URA.t := Auth.t (Excl.t (Any.t * Any.t)).
  Definition inv_black (mp_src mp_tgt: Any.t): (@URA.car invRA)
    := Auth.black (M:=(Excl.t _)) (Some (mp_src, mp_tgt)).
  Definition inv_white (mp_src mp_tgt: Any.t): (@URA.car invRA)
    := Auth.white (M:=(Excl.t _)) (Some (mp_src, mp_tgt)).

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.

  Definition inv_opener: iProp :=
    (∃ mp_src mp_tgt, OwnM (inv_white mp_src mp_tgt))%I.
  Definition inv_closed: iProp :=
    (∃ mp_src mp_tgt, OwnM (inv_black mp_src mp_tgt))%I.
  Definition inv_closer (mp_src mp_tgt: Any.t): iProp :=
    OwnM (inv_black mp_src mp_tgt)%I.
  Definition inv_open (mp_src mp_tgt: Any.t): iProp :=
    OwnM (inv_white mp_src mp_tgt)%I.



  Lemma inv_opening mp_src mp_tgt
    :
      inv_opener -∗ inv_closed -∗ #=> (inv_closer mp_src mp_tgt ** inv_open mp_src mp_tgt).
  Proof.
    unfold inv_opener, inv_closed, inv_open, inv_closer, inv_white, inv_black.
    iIntros "H0 H1".
    iDestruct "H0" as (mp_src0 mp_tgt0) "H0".
    iDestruct "H1" as (mp_src1 mp_tgt1) "H1".
    iCombine "H1 H0" as "H".
    iPoseProof (OwnM_Upd with "H") as "H".
    { instantiate (1:=Auth.black (Some (mp_src, mp_tgt): Excl.t _) ⋅ Auth.white (Some (mp_src, mp_tgt): Excl.t _)).
      eapply Auth.auth_update. ii. des. split.
      { ur. ss. }
      { ur. ur in FRAME. des_ifs. }
    }
    { iMod "H". iModIntro. iDestruct "H" as "[H0 H1]". iFrame. }
  Qed.

  Lemma inv_closing mp_src0 mp_tgt0 mp_src1 mp_tgt1
    :
      inv_closer mp_src0 mp_tgt0 -∗ inv_open mp_src1 mp_tgt1 -∗ #=> (inv_opener ** inv_closed).
  Proof.
    unfold inv_opener, inv_closed, inv_open, inv_closer, inv_white, inv_black.
    iIntros "H0 H1".
    iCombine "H0 H1" as "H".
    iPoseProof (OwnM_Upd with "H") as "H".
    { instantiate (1:=Auth.black (Some (mp_src0, mp_tgt0): Excl.t _) ⋅ Auth.white (Some (mp_src0, mp_tgt0): Excl.t _)).
      eapply Auth.auth_update. ii. des. split.
      { ur. ss. }
      { ur. ur in FRAME. des_ifs. }
    }
    { iMod "H". iDestruct "H" as "[H0 H1]".
      iModIntro. iSplitL "H1".
      { iExists _, _. ss. }
      { iExists _, _. ss. }
    }
  Qed.

  Lemma inv_open_unique mp_src mp_tgt
    :
      inv_opener -∗ inv_open mp_src mp_tgt -∗ False
  .
  Proof.
    unfold inv_opener, inv_closed, inv_open, inv_closer, inv_white, inv_black.
    iIntros "H0 H1". iDestruct "H0" as (mp_src0 mp_tgt0) "H0".
    iCombine "H0 H1" as "H". iOwnWf "H" as WF. exfalso.
    repeat ur in WF. ss.
  Qed.

  Lemma inv_close_unique mp_src mp_tgt
    :
      inv_closer mp_src mp_tgt -∗ inv_closed -∗ False
  .
  Proof.
    unfold inv_opener, inv_closed, inv_open, inv_closer, inv_white, inv_black.
    iIntros "H0 H1". iDestruct "H1" as (mp_src0 mp_tgt0) "H1".
    iCombine "H0 H1" as "H". iOwnWf "H" as WF. exfalso.
    repeat ur in WF. ss.
  Qed.

  Lemma inv_merge mp_src0 mp_tgt0 mp_src1 mp_tgt1
    :
      inv_closer mp_src0 mp_tgt0 -∗ inv_open mp_src1 mp_tgt1 -∗ ⌜mp_src1 = mp_src0 /\ mp_tgt1 = mp_tgt0⌝
  .
  Proof.
    unfold inv_opener, inv_closed, inv_open, inv_closer, inv_white, inv_black.
    iIntros "H0 H1".
    iCombine "H0 H1" as "H". iOwnWf "H" as WF. iPureIntro.
    eapply Auth.auth_included in WF. des.
    eapply Excl.extends in WF; ss.
    - des; clarify.
    - ur; ss.
  Qed.

  Definition inv_wf
             A
             (R_src: A -> Any.t -> Any.t -> iProp)
             (R_tgt: A -> Any.t -> Any.t -> iProp)
    : (((Σ * Any.t)) * ((Σ * Any.t)) -> Prop) :=
    @mk_wf
      _
      (A + Any.t * Any.t)
      (fun a' mp_src mp_tgt =>
         match a' with
         | inl a => inv_closed ** R_src a mp_src mp_tgt
         | inr (mp_src1, mp_tgt1) => inv_open mp_src1 mp_tgt1 ** ⌜mp_src1 = mp_src /\ mp_tgt1 = mp_tgt⌝
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
             inv_opener
               **
               (fst (PQ x) varg o)),
          (fun vret =>
             inv_opener
               **
               (snd (PQ x) vret)))
      ).
End AUX.

Ltac iarg :=
  let PRE := constr:("PRE") in
  let INV := constr:("INV") in
  let OPENER := constr:("☃OPENER") in
  let CLOSED := constr:("☃CLOSED") in
  let ARG := constr:("ARG") in
  eapply (@harg_clo _ PRE INV);
  [eassumption
  |
  ];
  let a := fresh "a" in
  intros a; i;
  mDesAndPureR PRE as PRE ARG;
  let EQ := fresh "EQ" in
  mPure ARG as EQ;
  try (destruct EQ);
  mDesSep PRE as OPENER PRE;
  destruct a as [?|[?mp_src ?mp_tgt]]; simpl;
  [mDesSep INV as CLOSED INV
  |mAssertPure False; ss; iDestruct "INV" as "[INV _]"; iApply (inv_open_unique with "☃OPENER INV")].

Ltac open_inv :=
  mAssert _ with "☃OPENER ☃CLOSED" as "☃TMP";
  [ iApply (inv_opening with "☃OPENER ☃CLOSED"); fail
   |mUpd "☃TMP"; mDesSep "☃TMP" as "☃CLOSER" "☃OPEN"].

Ltac close_inv :=
  mAssert _ with "☃CLOSER ☃OPEN" as "☃TMP";
  [ iApply (inv_closing with "☃CLOSER ☃OPEN"); fail
   |mUpd "☃TMP"; mDesSep "☃TMP" as "☃OPENER" "☃CLOSED"].

Tactic Notation "icall_open" uconstr(o) uconstr(x) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := constr:("☃OPEN") in
  let Hns := select_ihyps Hns in
  let Hns := constr:("☃OPEN"::Hns) in
  eapply (@hcall_clo _ Hns POST INV o _ x _ (inr (_, _)));
  unshelve_goal;
  [eassumption
  |
  |start_ipm_proof; iFrame "☃OPEN"; iSplitR; [ss|]
  |eauto with ord_step
  |
  |on_current ltac:(fun H => try clear H);
   intros ? ? ? ? ? ? [|[?mp_src ?mp_tgt]]; i; simpl;
   on_current ltac:(fun H => simpl in H);
   [mDesSep "☃OPEN" as "☃CLOSED" "☃TMP";
    mAssertPure False; ss; iApply (inv_close_unique with "☃CLOSER ☃CLOSED")
   |mDesSep "☃OPEN" as "☃OPEN" "☃TMP"; mPure "☃TMP" as [[] []]
   ]
  ].

Tactic Notation "icall_weaken" uconstr(ftsp) uconstr(o) uconstr(x) uconstr(a) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := get_fresh_name_tac "INV" in
  let CLOSED := constr:("☃CLOSED") in
  let OPENER := constr:("☃OPENER") in
  let Hns := select_ihyps Hns in
  let Hns := constr:("☃CLOSED"::"☃OPENER"::Hns) in
  eapply (@hcall_clo_weaken _ Hns POST INV _ _ ftsp o x _ (inl a));
  unshelve_goal;
  [|
   eassumption
   |
   |start_ipm_proof
    ; iFrame "☃CLOSED ☃OPENER"
   (* ; iSplitR; [ss|] *)
   |eauto with ord_step
   |
   |on_current ltac:(fun H => try clear H);
    intros ? ? ? ? ? ? [|[?mp_src ?mp_tgt]]; i; simpl;
    on_current ltac:(fun H => simpl in H);
    [mDesSep INV as "☃CLOSED" INV;
     mDesAndPureR POST as POST "☃TMP";
     let EQ := fresh in
     mPure "☃TMP" as EQ; inversion EQ;
     mDesSep POST as "☃OPENER" POST
    |mDesSep INV as "☃CLOSED" INV;
     mDesAndPureR POST as POST "☃TMP";
     mDesSep POST as "☃OPENER" POST;
     mAssertPure False; [iApply (inv_open_unique with "☃OPENER ☃CLOSED")|ss
    ]]
  ].

Tactic Notation "iret" uconstr(a) :=
  eapply (@hret_clo _ _ (inl a)); unshelve_goal;
  [eauto with ord_step
  |eassumption
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

  Definition mrec_spec (f: nat -> nat) (INV: iProp): ftspec (list val) val :=
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
