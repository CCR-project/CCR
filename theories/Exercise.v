Require Import sflib.
Require Import Universe.
Require Import Semantics.
From Paco Require Import paco.
Require Import RelationClasses List.
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.

CoInductive t: Type :=
(* | done *)
| cons (hd: nat) (tl: t)
.

Infix "##" := cons (at level 60, right associativity).
(*** past -------------> future ***)
(*** a ## b ## c ## spin / done ***)

Inductive _fintau (fintau: t -> Prop): t -> Prop :=
| fintau_tau
    tl
    (TL: _fintau fintau tl)
  :
    _fintau fintau (0 ## tl)
| fintau_ev
    hd tl
    (EV: hd <> 0)
    (TL: fintau tl)
  :
    _fintau fintau (hd ## tl)
.

Definition fintau: _ -> Prop := paco1 _fintau bot1.

Lemma fintau_mon: monotone1 _fintau.
Proof.
  ii. induction IN; econs; eauto.
Qed.

Hint Constructors _fintau.
Hint Unfold fintau.
Hint Resolve fintau_mon: paco.




Inductive _fintau2 (fintau2: nat -> t -> Prop): nat -> t -> Prop :=
| fintau2_tau
    fuel tl
    (TL: fintau2 fuel tl)
  :
    _fintau2 fintau2 (S fuel) (0 ## tl)
| fintau2_ev
    fuel fuel_new hd tl
    (EV: hd <> 0)
    (TL: fintau2 fuel_new tl)
  :
    _fintau2 fintau2 fuel (hd ## tl)
.

Definition fintau2: _ -> _ -> Prop := paco2 _fintau2 bot2.

Lemma fintau2_mon: monotone2 _fintau2.
Proof.
  ii. induction IN; econs; eauto.
Qed.

Hint Constructors _fintau2.
Hint Unfold fintau2.
Hint Resolve fintau2_mon: paco.



Inductive maxfuel: t -> nat -> Prop :=
| maxfuel_tau
    fuel tl
    (TL: maxfuel tl fuel)
  :
    maxfuel (0 ## tl) (S fuel)
| maxfuel_ev
    hd tl
    (EV: hd <> 0)
  :
    maxfuel (hd ## tl) 0
.

Inductive _sim (sim: t -> t -> Prop): t -> t -> Prop :=
| sim_cons
    hd tl0 tl1
    (TL: sim tl0 tl1)
  :
    _sim sim (hd ## tl0) (hd ## tl1)
.

Definition sim: _ -> _ -> Prop := paco2 _sim bot2.

Lemma sim_mon: monotone2 _sim.
Proof.
  ii. induction IN; econs; eauto.
Qed.

Hint Constructors _sim.
Hint Unfold sim.
Hint Resolve sim_mon: paco.

Axiom sim_eq: sim = eq.

CoFixpoint spin := cons 0 spin.

Definition unfolder (tr: t): t :=
  match tr with
  (* | done => done *)
  | cons hd tl => cons hd tl
  end
.

Lemma unfold_t tr: tr = unfolder tr. Proof. destruct tr; ss. Qed.

Theorem diverge_spin
        tr
        (DIVERGE: forall n, ~maxfuel tr n)
  :
    tr = spin
.
Proof.
  rewrite <- sim_eq. generalize dependent tr. pcofix CIH. i.
  pfold. rewrite unfold_t. ss. destruct tr; ss.
  destruct hd.
  - econs; eauto. right. eapply CIH; eauto. ii. eapply (DIVERGE (S n)).
    { clear - H.
      ginduction n; i; eauto.
      + inv H. econs; eauto. econs; eauto.
      + inv H. econs; eauto.
    }
  - exfalso. eapply (DIVERGE 0). econs; eauto.
Qed.

Theorem case_analysis
        tr
  :
    <<SPIN: tr = spin>> \/ <<MAX: exists n, maxfuel tr n>>
.
Proof.
  destruct (classic (exists n, maxfuel tr n)); eauto.
  left.
  eapply diverge_spin.
  ii.
  eapply Classical_Pred_Type.not_ex_all_not with (n:=n) in H. eauto.
Qed.

Theorem fintau_nospin: fintau spin -> False.
Proof.
  i. punfold H. inv H.
  - rewrite unfold_t in H1. ss. clarify.
    revert TL. fix IH 1. i. inv TL; ss.
    + rewrite unfold_t in H0. ss; clarify. Guarded.
    + rewrite unfold_t in H0. ss; clarify. Guarded.
  - rewrite unfold_t in H1. ss. clarify.
Qed.

Theorem equiv
        tr
  :
    fintau tr <-> exists fuel, fintau2 fuel tr
.
Proof.
  split; i.
  { destruct (case_analysis tr).
    - des; clarify. exfalso. eapply fintau_nospin; eauto.
    - des. rename H into A. rename H0 into B. exists n. revert_until tr. revert tr.
      pcofix CIH. i. pfold. punfold A.
      revert tr A B. induction n; i.
      + inv B. inv A; ss. pclearbot.
        destruct (case_analysis tl).
        * des; clarify. exfalso. eapply fintau_nospin; eauto.
        * des; clarify. econs; eauto.
      + inv B. inv A; ss. econs; eauto.
  }
  { des. rename H into A. revert_until tr. revert tr.
    pcofix CIH. i. pfold. punfold A.
    revert A. revert tr. induction fuel; i.
    - inv A. econs; eauto. pclearbot. right. eauto.
    - inv A.
      + pclearbot. punfold TL.
      + pclearbot. econs; eauto.
  }
Qed.
