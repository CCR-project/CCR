Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.
Set Typeclasses Depth 5.




Global Opaque GRA.to_URA.
Infix "⋅" := URA.add (at level 50, left associativity).
Notation "(⋅)" := URA.add (only parsing).


Definition unleftU {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
  match xy with
  | inl x => Ret x
  | inr y => triggerUB
  end.

Definition unleftN {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
  match xy with
  | inl x => Ret x
  | inr y => triggerNB
  end.

Definition unrightU {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
  match xy with
  | inl x => triggerUB
  | inr y => Ret y
  end.

Definition unrightN {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
  match xy with
  | inl x => triggerNB
  | inr y => Ret y
  end.

Section UNPADDING.
  
  Definition unpadding A {Σ} `{@GRA.inG A Σ} (a: URA.car (t:=Σ)): itree Es (URA.car (t:=A)) :=
    assume(forall n (NEQ: n <> GRA.inG_id), a n = URA.unit);;
    Ret (eq_rect_r (@URA.car) (a GRA.inG_id) GRA.inG_prf)
  .

  Definition unpadding2 {A Σ} `{@GRA.inG A Σ} (a: URA.car (t:=Σ)): itree Es (URA.car (t:=A)) :=
    n <- trigger (Choose _);;
    (if Nat.eq_dec GRA.inG_id n
     then Ret tt
     else  assume (a n = URA.unit);; Ret tt);;
    Ret (eq_rect_r (@URA.car) (a GRA.inG_id) GRA.inG_prf)
  .

End UNPADDING.
Arguments unpadding _ {Σ H}.






















Section IRIS.
  Context {Σ: GRA.t}.
  Definition iProp := Σ -> Prop.
  Definition Sepconj (P Q: iProp): iProp :=
    fun r => exists a b, r = URA.add a b /\ P a /\ Q b
  .
  Definition Pure (P: Prop): iProp := fun _ => P.
  Definition Ex {X: Type} (P: X -> iProp): iProp := fun r => exists x, P x r.
  Definition Own (r0: Σ): iProp := fun r1 => URA.extends r0 r1.
  Definition And (P Q: iProp): iProp := fun r => P r /\ Q r.
  Definition Or (P Q: iProp): iProp := fun r => P r \/ Q r.
  (* Definition Own (r0: Σ): iProp := fun r1 => r0 = r1. *)

  Definition Impl (P Q: iProp): Prop := P <1= Q.
  Infix "i->" := Impl (at level 60).
  Notation "P 'i<->' Q" := ((Impl P Q) /\ (Impl Q P)) (at level 60).

  Lemma Own_extends
        (a b: Σ)
        (EXT: URA.extends a b)
    :
      (Own b) i-> (Own a)
  .
  Proof. ii. ss. r in PR. r. etrans; et. Qed.

  Lemma Iff_eq
        P Q
        (IFF: P i<-> Q)
    :
      P = Q
  .
  Proof.
    apply func_ext. i. apply prop_ext. des. split; i; et.
  Qed.

  Lemma own_sep'
        (r0 r1 r2: Σ)
        (ADD: r0 = r1 ⋅ r2)
    :
      Own r0 = Sepconj (Own r1) (Own r2)
  .
  Proof.
    apply Iff_eq.
    split; ii.
    - clarify. r in PR. r. r in PR. des. exists r1, (r2 ⋅ ctx). esplits; et.
      + rewrite URA.add_assoc. ss.
      + refl.
      + rr. esplits; et.
    - r in PR. r. des. clarify. r in PR0. r in PR1. etrans.
      { eapply URA.extends_add; et. }
      rewrite ! (URA.add_comm a).
      eapply URA.extends_add; et.
  Qed.

  Lemma own_sep
        (r1 r2: Σ)
    :
      Own (r1 ⋅ r2) = Sepconj (Own r1) (Own r2)
  .
  Proof.
    erewrite <- own_sep'; et.
  Qed.

End IRIS.

Infix "**" := Sepconj (at level 60).
Infix "∧" := And (at level 60).
Infix "∨" := Or (at level 60).
Notation "'⌜' P '⌝'" := (Pure P).
Notation "'Exists' x .. y , p" := (Ex (fun x => .. (Ex (fun y => p)) ..))
                                    (at level 200, x binder, right associativity,
                                     format "'[' 'Exists'  '/  ' x  ..  y ,  '/  ' p ']'").














(* Definition until (n: nat): list nat := mapi (fun n _ => n) (List.repeat tt n). *)


(*** TODO: move to Coqlib ***)
Definition map_fst A B C (f: A -> C): A * B -> C * B := fun '(a, b) => (f a, b).
Definition map_snd A B C (f: B -> C): A * B -> A * C := fun '(a, b) => (a, f b).


(** TODO: move to PCM.v **)
Declare Scope ra_scope.
Delimit Scope ra_scope with ra.
Notation " K ==> V' " := (URA.pointwise K V'): ra_scope.

















Section IPM.
  Context {Σ: GRA.t}.
  Definition iHyp (P: Σ -> Prop) (r: Σ): Prop := P r.

  Lemma intro_iHyp: forall P r, P r = iHyp P r.
    { i. unfold iHyp. apply prop_ext. split; i; des; et. }
  Qed.

  Lemma wf_split: forall (a b: Σ), URA.wf (a ⋅ b) -> URA.wf a /\ URA.wf b.
    { i. split; eapply URA.wf_mon; et. rewrite URA.add_comm; et. }
  Qed.

  Lemma sepconj_merge: forall (a b: Σ) (Pa Pb: iProp), iHyp Pa a -> iHyp Pb b -> iHyp (Pa ** Pb) (a ⋅ b).
  Proof. i. rr. esplits; eauto. Qed.

  Lemma sepconj_split: (forall (ab : Σ) (Pa Pb : iProp), iHyp (Pa ** Pb) (ab) -> exists a b, iHyp Pa a /\ iHyp Pb b /\ ab = a ⋅ b).
    { clear - Σ. ii. unfold iHyp in *. r in H. destruct H. des. esplits; et. }
  Qed.

End IPM.











(* Definition iApp (P: Σ -> Prop) (r: Σ): Prop := P r /\ URA.wf r. *)
(* Notation "'ᐸ ' P ' ᐳ'" := (iApp P _) (at level 60). (* (format "'ᐸ'  P  'ᐳ'") *) *)
Notation "'ᐸ' P 'ᐳ'" := (iHyp P _) (at level 60). (* (format "'ᐸ'  P  'ᐳ'") *)

Ltac iSimplWf :=
  repeat match goal with
         | [H: URA.wf (?a ⋅ ?b) |- _ ] =>
           repeat (try rewrite URA.unit_id in H; try rewrite URA.unit_idl in H);
           apply wf_split in H; destruct H
         end.

(* Definition iEnv: Type := list (iProp * Σ). *)
(* Definition iEnvWf: iEnv -> Prop := fun ie => URA.wf (List.fold_left (⋅) (List.map snd ie) ε). *)

Ltac on_first_hyp tac :=
  match reverse goal with [ H : _ |- _ ] => first [ tac H | fail 1 ] end.

Definition IPROPS: Prop := forall x, x - x = 0.
Lemma IPROPS_intro: IPROPS. r. i. rewrite Nat.sub_diag. ss. Qed.

Ltac to_bar TAC :=
  match goal with
  | [H: IPROPS |- _ ] => TAC H
  | _ => idtac
  end.

Ltac bar :=
  to_bar ltac:(fun _ => fail 1);
  let NAME := fresh "ㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡ" in
  assert (NAME : IPROPS) by (exact IPROPS_intro)
.

Goal False.
  bar. clear_tac. Fail bar.
Abort.

Ltac r_length ls :=
  match ls with
  | (?x ⋅ ?y) =>
    let xl := r_length x in
    let yl := r_length y in
    constr:(xl + yl)
  | _ => constr:(1)
  end.

Ltac r_in r rs :=
  match rs with
  | r => idtac
  | (r ⋅ ?y) => idtac
  | (?x ⋅ r) => idtac
  | (?x ⋅ ?y) => r_in r x + r_in r y
  | _ => fail
  end.

Ltac r_contains xs ys :=
  match xs with
  | (?x0 ⋅ ?x1) => r_contains x0 ys; r_contains x1 ys
  | _ => r_in xs ys
  end.

Ltac iClears := match goal with
                | [ |- iHyp _ ?rgoal ] =>
                  repeat multimatch goal with
                         | [ H: iHyp _ ?r |- _ ] =>
                           tryif r_contains r rgoal
                           then idtac
                           else clear H
                         end
                end.

Ltac clear_bar := to_bar ltac:(fun H => clear H).

Ltac iRefresh :=
  clear_bar;
  bar;
  repeat multimatch goal with
         | [H: URA.extends ?a ?b |- _ ] => replace (URA.extends a b) with ((Own a) b) in H by reflexivity
         | [H: iHyp _ _ |- _ ] => revert H
         (*** TODO: move existing resources to top ***)
         (*** TODO: remove redundant URA.wf ***)
         | [H: ?ip ?r |- _ ] =>
           match type of ip with
           | iProp => rewrite intro_iHyp in H; move r at top; move H at bottom
           | _ => idtac
           end
         end;
  i;
  try (match goal with
       | [ |- ?ip ?r ] =>
         match type of ip with
         | iProp => rewrite intro_iHyp
         | _ => idtac
         end
       end;
       iClears)
.

Ltac pcm_solver := idtac.

Ltac iMerge H0 G0 :=
  match goal with
  | [H: iHyp ?ph ?rh |- _ ] =>
    check_equal H H0;
    match goal with
    | [G: iHyp ?pg ?rg |- _ ] =>
      check_equal G G0;
      let name := fresh "tmp" in
      rename H into name;
      assert(H: iHyp (ph ** pg) (rh ⋅ rg)) by (apply sepconj_merge; try assumption);
      clear name; clear G
    end
  end
.

Ltac iApply H := erewrite f_equal; [apply H|pcm_solver].

Ltac idtacs Hs :=
  match Hs with
  | (?H0, ?H1) => idtacs H0; idtacs H1
  | ?H => idtac H
  end
.

Ltac r_gather Hs :=
  match Hs with
  | (?H0, ?H1) =>
    let rs0 := r_gather H0 in
    let rs1 := r_gather H1 in
    constr:(rs0 ⋅ rs1)
  | ?H =>
    match (type of H) with
    | iHyp _ ?rh => constr:(rh)
    end
      (* match goal with *)
      (* | [G: iHyp ?ph ?rh |- _ ] => *)
      (*   check_equal H G; *)
      (*   constr:(rh) *)
      (* end *)
  end.

Ltac iSplit Hs0 Hs1 :=
  match goal with
  | [ |- iHyp (?ph ** ?pg) _ ] =>
    let tmp0 := (r_gather Hs0) in
    let tmp1 := (r_gather Hs1) in
    erewrite f_equal; cycle 1; [instantiate (1:= tmp0 ⋅ tmp1)|eapply sepconj_merge; iClears]
  end
.

Ltac iDestruct H :=
  match type of H with
  | iHyp (Exists _, _) _ => destruct H as [? H]; iRefresh
  | iHyp (_ ** _) _ =>
    let name0 := fresh "A" in
    apply sepconj_split in H as [? [? [H [name0 ?]]]]; iRefresh
  end.

Ltac iPure H := rr in H; to_bar ltac:(fun BAR => move H after BAR). (* ; iRefresh. *)

Ltac iExists H :=
  match (type of H) with
  | iHyp ?P ?r => exists r
  end.












Section IPMTEST.
  Context {Σ: GRA.t}.
  Goal forall (a b c: Σ), False.
    i.
    let n := r_length (a ⋅ b ⋅ c) in pose n.

    (r_in a (a ⋅ b ⋅ c)).
    (r_in b (a ⋅ b ⋅ c)).
    (r_in c (a ⋅ b ⋅ c)).
    (r_in a (a ⋅ b)).
    (r_in b (a ⋅ b)).
    Fail (r_in c (a ⋅ b)).
    Fail (r_in a (b)).
    (r_in b (b)).
    Fail (r_in c (b)).

    (r_contains a (a ⋅ b ⋅ c)).
    (r_contains b (a ⋅ b ⋅ c)).
    (r_contains c (a ⋅ b ⋅ c)).
    (r_contains a (a ⋅ b)).
    (r_contains b (a ⋅ b)).
    Fail (r_contains c (a ⋅ b)).
    Fail (r_contains a (b)).
    (r_contains b (b)).
    Fail (r_contains c (b)).

    (r_contains (a ⋅ b) (a ⋅ b ⋅ c)).
    (r_contains (b ⋅ a) (a ⋅ b ⋅ c)).
    (r_contains (b ⋅ c) (a ⋅ b ⋅ c)).
    (r_contains (c ⋅ a ⋅ b) (a ⋅ b ⋅ c)).
    Fail (r_contains (c ⋅ a ⋅ b) (a ⋅ b)).
    Fail (r_contains (a ⋅ c) (a ⋅ b)).
  Abort.

  Goal forall (a b: Σ) (Pa Pb: iProp), Pa a -> Pb b -> URA.wf (a ⋅ b) -> (Pa ** Pb) (b ⋅ a).
    i. iRefresh.
    iMerge H H0.
    iApply H.
    rewrite URA.add_comm. ss.
  Qed.


  Goal forall (a b c: Σ) (Pa Pb Pc: iProp), Pa a -> Pb b -> Pc c -> URA.wf (a ⋅ b ⋅ c) -> (Pa ** Pc ** Pb) (c ⋅ b ⋅ a).
    i. iRefresh.
    iSplit (H, H1) H0.
    { admit "pcm solver". }
    admit "okay".
    admit "okay".
  Abort.
End IPMTEST.












Section PROOF.
  Context {Σ: GRA.t}.
  (*** TODO: move to proper place, together with "mk_simple" ***)
  (*** TODO: rename sb into spb ***)
  (*** TODO: remove redundancy with Hoareproof0.v ***)


  (*** TODO: write use below (commented) iProp version instead ***)
  Definition mk_simple (mn: string) {X: Type} (P: X -> Any.t -> ord -> Σ -> Prop) (Q: X -> Any.t -> Σ -> Prop): fspec :=
    @mk _ mn X (list val) (val) (fun x y a o r => P x a o r /\ y↑ = a) (fun x z a r => Q x a r /\ z↑ = a)
  .
  (* Definition mk_simple (mn: string) {X: Type} (P: X -> Any.t -> ord -> Σ -> Prop) (Q: X -> Any.t -> Σ -> Prop): fspec := *)
  (*   @mk _ mn X (list val) (val) (fun x y a o => P x a o ∧ ⌜y↑ = a⌝) (fun x z a => Q x a ∧ ⌜z↑ = a⌝) *)
  (* . *)
  Definition mk_sb_simple (mn: string) {X: Type} (P: X -> Any.t -> ord -> Σ -> Prop) (Q: X -> Any.t -> Σ -> Prop)
             (body: list val -> itree (hCallE +' pE +' eventE) val): fspecbody := mk_specbody (mk_simple mn P Q) body.

End PROOF.
