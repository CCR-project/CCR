Require Export ZArith.
Require Export String.

From ExtLib Require Export
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import sflib.
Require Import Coqlib.


Set Implicit Arguments.


Global Opaque string_dec.

(************ temporary buffer before putting it in Coqlib ***********)
(************ temporary buffer before putting it in Coqlib ***********)
(************ temporary buffer before putting it in Coqlib ***********)

Class Dec (A: Type) := dec: forall (a0 a1: A), { a0 = a1 } + { a0 <> a1 }.

Global Program Instance positive_Dec: Dec positive. Next Obligation. decide equality. Defined.
Global Program Instance string_Dec: Dec String.string. Next Obligation. apply String.string_dec. Defined.
Global Program Instance nat_Dec: Dec nat. Next Obligation. apply Nat.eq_dec. Defined.
Global Program Instance Z_Dec: Dec Z. Next Obligation. apply Z.eq_dec. Defined.

Definition update K `{Dec K} V (f: K -> V) (k: K) (v: V): K -> V :=
  fun _k => if dec k _k then v else f _k.

(************ temporary buffer before putting it in Coqlib ***********)
(************ temporary buffer before putting it in Coqlib ***********)
(************ temporary buffer before putting it in Coqlib ***********)


Global Instance function_Map `{Dec K} V: (Map K V (K -> option V)) :=
  Build_Map
    (fun _ => None)
    (fun k0 v m => fun k1 => if dec k0 k1 then Some v else m k1)
    (fun k0 m => fun k1 => if dec k0 k1 then None else m k1)
    (fun k m => m k)
    (fun m0 m1 => fun k => match (m0 k) with
                           | Some v => Some v
                           | _ => m1 k
                           end).


Global Instance Dec_RelDec K `{Dec K}: @RelDec K eq :=
  { rel_dec := dec }.

Global Instance Dec_RelDec_Correct K `{Dec K}: RelDec_Correct Dec_RelDec.
Proof.
  unfold Dec_RelDec. ss.
  econs. ii. ss. unfold Dec_RelDec. split; ii.
  - unfold rel_dec in *. unfold sumbool_to_bool in *. des_ifs.
  - unfold rel_dec in *. unfold sumbool_to_bool in *. des_ifs.
Qed.

Fixpoint alist_pop (K : Type) (R : K -> K -> Prop) (RD_K : RelDec R) (V : Type)
         (k : K) (m : alist K V): option (V * alist K V) :=
  match m with
  | [] => None
  | (k', v) :: ms =>
    if k ?[R] k'
    then Some (v, ms)
    else match @alist_pop K R RD_K V k ms with
         | Some (v', ms') => Some (v', (k', v) :: ms')
         | None => None
         end
  end.

Fixpoint alist_pops (K : Type) (R : K -> K -> Prop) (RD_K : RelDec R) (V : Type)
         (k : list K) (m : alist K V): alist K V * alist K V :=
  match k with
  | [] => ([], m)
  | khd::ktl =>
    let (l, m0) := alist_pops RD_K ktl m in
    match alist_pop RD_K khd m0 with
    | Some (v, m1) => ((khd, v)::l, m1)
    | None => (l, m0)
    end
  end.

Fixpoint alist_replace (K : Type) (R : K -> K -> Prop) (RD_K : RelDec R) (V : Type)
         (k : K) (v: V) (m : alist K V): alist K V :=
  match m with
  | [] => []
  | (k', v') :: ms =>
    if k ?[R] k'
    then (k, v) :: ms
    else (k', v') :: alist_replace _ k v ms
  end.

Definition alist_filter K `{Dec K} V (f: K -> bool) (l: alist K V) :=
  List.filter (f ∘ fst) l.

Arguments alist_replace [K R] {RD_K} [V].
Arguments alist_find [K R] {RD_K} [V].
Arguments alist_add [K R] {RD_K} [V].
Arguments alist_pop [K R] {RD_K} [V].
Arguments alist_pops [K R] {RD_K} [V].
Arguments alist_remove [K R] {RD_K} [V].

Lemma eq_rel_dec_correct T `{DEC: Dec T}
      x0 x1
  :
    x0 ?[eq] x1 = if (DEC x0 x1) then true else false.
Proof.
  des_ifs.
Qed.

Require Import List Setoid Permutation Sorted Orders.

Section ALIST.
  Lemma alist_find_some K `{Dec K} V (k: K) (l: alist K V) (v: V)
        (FIND: alist_find k l = Some v)
  :
    In (k, v) l.
  Proof.
    revert FIND. induction l; ss.
    i. destruct a. ss. rewrite eq_rel_dec_correct in *. des_ifs; auto.
  Qed.

  Lemma alist_find_some_iff K `{Dec K} V (k: K) (l: alist K V) (v: V)
        (ND: NoDup (List.map fst l))
        (IN: In (k, v) l)
  :
    alist_find k l = Some v.
  Proof.
    revert ND IN. induction l; ss.
    i. destruct a. ss. inv ND. des.
    { clarify. rewrite eq_rel_dec_correct in *. des_ifs. }
    { rewrite eq_rel_dec_correct in *. des_ifs; et.
      exfalso. eapply (List.in_map fst) in IN. et. }
  Qed.

  Lemma alist_find_none K `{Dec K} V (k: K) (l: alist K V)
        (FIND: alist_find k l = None)
        v
    :
      ~ In (k, v) l.
  Proof.
    revert FIND. induction l; ss.
    i. destruct a. ss. rewrite eq_rel_dec_correct in *. des_ifs; auto.
    ii. des; clarify. eapply IHl; et.
  Qed.

  Lemma alist_find_app K `{Dec K} V (k: K) (l0 l1: alist K V) (v: V)
        (FIND: alist_find k l0 = Some v)
    :
      alist_find k (l0 ++ l1) = Some v.
  Proof.
    revert FIND. induction l0; ss.
    i. destruct a. ss. rewrite eq_rel_dec_correct in *. des_ifs; auto.
  Qed.

  Lemma alist_find_map K `{Dec K} V0 V1 (f: V0 -> V1) (k: K) (l: alist K V0)
    :
      alist_find k (List.map (fun '(k, v) => (k, f v)) l) = o_map (alist_find k l) f.
  Proof.
    induction l; ss. uo. destruct a. rewrite eq_rel_dec_correct in *.
    des_ifs.
  Qed.

  Lemma alist_find_find_some K `{Dec K} V (k: K) (l: alist K V) v
    :
      alist_find k l = Some v <-> find (fun '(k2, _) => rel_dec k k2) l = Some (k, v).
  Proof.
    induction l; ss. destruct a. rewrite eq_rel_dec_correct in *. des_ifs.
    split; i; clarify.
  Qed.

  Lemma alist_find_find_none K `{Dec K} V (k: K) (l: alist K V)
    :
      alist_find k l = None <-> find (fun '(k2, _) => rel_dec k k2) l = None.
  Proof.
    induction l; ss. destruct a. rewrite eq_rel_dec_correct in *. des_ifs.
  Qed.

  Lemma alist_add_find_eq K `{Dec K} V (k: K) (l: alist K V) (v: V)
    :
      alist_find k (alist_add k v l) = Some v.
  Proof.
    ss. rewrite eq_rel_dec_correct. des_ifs.
  Qed.

  Lemma alist_remove_find_eq K `{Dec K} V (k: K) (l: alist K V)
    :
      alist_find k (alist_remove k l) = None.
  Proof.
    induction l; ss. rewrite eq_rel_dec_correct. des_ifs.
    ss. destruct a. ss. rewrite eq_rel_dec_correct. des_ifs.
  Qed.

  Lemma alist_remove_find_neq K `{Dec K} V (k0 k1: K) (l: alist K V)
        (NEQ: k0 <> k1)
    :
      alist_find k0 (alist_remove k1 l) = alist_find k0 l.
  Proof.
    induction l; ss.
    destruct a. ss. rewrite ! eq_rel_dec_correct. des_ifs.
    { ss. rewrite eq_rel_dec_correct. des_ifs. }
    { ss. rewrite eq_rel_dec_correct. des_ifs. }
  Qed.

  Lemma alist_add_find_neq K `{Dec K} V (k0 k1: K) (l: alist K V) (v: V)
        (NEQ: k0 <> k1)
    :
      alist_find k0 (alist_add k1 v l) = alist_find k0 l.
  Proof.
    ss. rewrite eq_rel_dec_correct. des_ifs.
    eapply alist_remove_find_neq; auto.
  Qed.

  Lemma alist_find_filter K `{Dec K} V (l: alist K V) (k: K) (v: V) (f: K -> bool)
        (FIND: alist_find k (alist_filter f l) = Some v)
        (ND: NoDup (List.map fst l))
    :
      alist_find k l = Some v.
  Proof.
    revert FIND ND. induction l; ss. i.
    destruct a. erewrite eq_rel_dec_correct. ss. inv ND. des_ifs.
    - ss. rewrite eq_rel_dec_correct in *. des_ifs.
    - exfalso. hexploit IHl; et. i. eapply H2.
      eapply alist_find_some in H0. eapply (in_map fst) in H0. ss.
    - ss. rewrite eq_rel_dec_correct in *. des_ifs.
      eapply IHl; et.
    - eapply IHl; et.
  Qed.

  Lemma alist_add_nodup K `{Dec K} V (l: alist K V) k v
        (ND: NoDup (List.map fst l))
    :
      NoDup (List.map fst (alist_add k v l)).
  Proof.
    revert ND. induction l; ss.
    { i. econs; et. }
    i. inv ND. spc IHl. destruct a. ss.
    rewrite eq_rel_dec_correct in *. des_ifs.
    inv IHl. ss. econs; et.
    { ii. ss. des; clarify. }
    { econs; et. ii. eapply H2.
      eapply in_map_iff in H0. eapply in_map_iff.
      des. subst. esplits; et.
      unfold alist_remove in H1.
      eapply filter_In in H1. des; auto. }
  Qed.

  Lemma alist_remove_filter K `{Dec K} V (l: alist K V) k f
    :
      alist_filter f (alist_remove k l) =
      alist_remove k (alist_filter f l).
  Proof.
    induction l; ss. destruct a. ss.
    rewrite eq_rel_dec_correct. des_ifs; ss.
    { rewrite Heq0. rewrite eq_rel_dec_correct. des_ifs. f_equal; et. }
    { rewrite Heq0. et. }
    { rewrite eq_rel_dec_correct. des_ifs. }
  Qed.

  Lemma alist_add_filter K `{Dec K} V (l: alist K V) k v f
        (IN: f k = true)
    :
      alist_filter f (alist_add k v l) =
      alist_add k v (alist_filter f l).
  Proof.
    unfold alist_add in *. ss. des_ifs.
    f_equal. eapply alist_remove_filter.
  Qed.

  Lemma alist_add_other_filter K `{Dec K} V f (l: alist K V) k v
        (NIN: f k = false)
    :
      alist_filter f (alist_add k v l) =
      alist_filter f l.
  Proof.
    induction l; ss.
    { i. rewrite NIN. ss. }
    { i. destruct a. ss. rewrite NIN in *.
      rewrite eq_rel_dec_correct. des_ifs; ss.
      { rewrite Heq0. f_equal. auto. }
      { rewrite Heq0. auto. }
    }
  Qed.

  Lemma alist_permutation_find K `{Dec K} V (l0 l1: alist K V)
        (ND: NoDup (List.map fst l0))
        (PERM: Permutation l0 l1)
        k
    :
      alist_find k l0 = alist_find k l1.
  Proof.
    revert ND k. induction PERM; ss.
    { i. inv ND. destruct x. rewrite eq_rel_dec_correct. des_ifs. et. }
    { i. inv ND. inv H3. destruct x, y. rewrite eq_rel_dec_correct. des_ifs.
      rewrite eq_rel_dec_correct in *. des_ifs. f_equal. exfalso. eapply H2. ss. auto. }
    { i. rewrite IHPERM1; auto. rewrite IHPERM2; auto.
      eapply Permutation_NoDup; [|apply ND].
      eapply Permutation_map. auto.
    }
  Qed.

  Lemma alist_find_app_o K `{Dec K} V k (l0 l1: alist K V)
    :
      alist_find k (l0 ++ l1) =
      match (alist_find k l0) with
      | Some v => Some v
      | _ => alist_find k l1
      end.
  Proof.
    induction l0; ss. destruct a. rewrite eq_rel_dec_correct. des_ifs.
  Qed.

  Lemma alist_find_map_snd K R `{RD_K: @RelDec K R} A B (f: A -> B) (l: alist K A) k
    :
      alist_find k (map (map_snd f) l)
      =
      o_map (alist_find k l) f.
  Proof.
    induction l; ss. destruct a. ss. uo. des_ifs.
  Qed.
End ALIST.


Tactic Notation "asimpl" "in" ident(H) :=
  (try unfold alist_remove, alist_add in H); simpl in H.

Tactic Notation "asimpl" "in" "*" :=
  (try unfold alist_remove, alist_add in *); simpl in *.

Tactic Notation "asimpl" :=
  (try unfold alist_remove, alist_add); simpl.





Module Type TotalOrderBool <: TotalTransitiveLeBool'.
  Parameter t : Type.
  Parameter leb : t -> t -> bool.
  Parameter leb_total : forall x y : t, leb x y = true \/ leb y x = true.
  Parameter leb_trans : Transitive leb.

  Parameter eqA : t -> t -> Prop.
  Parameter eqb_eq : forall x y : t, eqA x y <-> leb x y = true /\ leb y x.
End TotalOrderBool.

Definition ascii_le (c0 c1: Ascii.ascii): bool :=
  (Ascii.nat_of_ascii c0 <=? Ascii.nat_of_ascii c1)%nat.

Lemma ascii_le_antisym c0 c1
      (EQ0: ascii_le c0 c1 = true)
      (EQ1: ascii_le c1 c0 = true)
  :
    c0 = c1.
Proof.
  unfold ascii_le in *.
  eapply leb_complete in EQ0.
  eapply leb_complete in EQ1.
  rewrite <- (Ascii.ascii_nat_embedding c0).
  rewrite <- (Ascii.ascii_nat_embedding c1). f_equal. lia.
Qed.

Fixpoint string_le (s0 s1: string): bool :=
  match s0, s1 with
  | EmptyString, _ => true
  | _, EmptyString => false
  | String hd0 tl0, String hd1 tl1 =>
    if (Ascii.eqb hd0 hd1)
    then string_le tl0 tl1
    else ascii_le hd0 hd1
  end.

Lemma string_le_antisym s0 s1
      (EQ0: string_le s0 s1 = true)
      (EQ1: string_le s1 s0 = true)
  :
    s0 = s1.
Proof.
  revert s1 EQ0 EQ1. induction s0; ss.
  { i. destruct s1; ss. }
  i. destruct s1; ss. des_ifs.
  { eapply Ascii.eqb_eq in Heq0. eapply Ascii.eqb_eq in Heq. subst.
    f_equal; auto. }
  { eapply Ascii.eqb_eq in Heq. subst. rewrite Ascii.eqb_refl in Heq0. ss. }
  { eapply Ascii.eqb_eq in Heq0. subst. rewrite Ascii.eqb_refl in Heq. ss. }
  { hexploit ascii_le_antisym.
    { eapply EQ0. }
    { eapply EQ1. }
    i. subst. rewrite Ascii.eqb_refl in Heq. ss.
  }
Qed.

Module AsciiOrder <: TotalOrderBool.
  Definition t := Ascii.ascii.
  Definition leb := ascii_le.
  Lemma leb_total : forall x y : t, leb x y = true \/ leb y x = true.
  Proof.
    i. unfold leb, ascii_le.
    assert (Ascii.nat_of_ascii x <= Ascii.nat_of_ascii y \/ Ascii.nat_of_ascii y <= Ascii.nat_of_ascii x)%nat by lia.
    des.
    { left. eapply leb_correct. auto. }
    { right. eapply leb_correct. auto. }
  Qed.

  Lemma leb_trans : Transitive leb.
  Proof.
    ii. unfold leb, ascii_le in *. unfold is_true in *.
    eapply leb_complete in H. eapply leb_complete in H0.
    eapply leb_correct. auto. etrans; et.
  Qed.

  Definition eqA: t -> t -> Prop := eq.

  Lemma eqb_eq : forall x y : t, eqA x y <-> leb x y = true /\ leb y x.
  Proof.
    i. split.
    { i. inv H. destruct (leb_total y y); auto. }
    { i. des. eapply ascii_le_antisym; auto. }
  Qed.
End AsciiOrder.

Module StringOrder <: TotalOrderBool.
  Definition t := string.
  Definition leb := string_le.
  Lemma leb_total : forall x y : t, leb x y = true \/ leb y x = true.
  Proof.
    i. unfold leb. revert y. induction x; ss; auto.
    i. des_ifs; ss; auto.
    { eapply Ascii.eqb_eq in Heq. subst.
      rewrite Ascii.eqb_refl. auto. }
    { rewrite Ascii.eqb_sym. rewrite Heq.
      eapply AsciiOrder.leb_total. }
  Qed.

  Lemma leb_trans : Transitive leb.
  Proof.
    ii. unfold leb in *. revert y z H H0.
    induction x; ss. i. destruct y, z; ss.
    destruct (Ascii.eqb a a0) eqn:EQ0.
    { eapply Ascii.eqb_eq in EQ0. subst. des_ifs. et. }
    destruct (Ascii.eqb a0 a1) eqn:EQ1.
    { eapply Ascii.eqb_eq in EQ1. subst. des_ifs. }
    destruct (Ascii.eqb a a1) eqn:EQ2.
    { eapply Ascii.eqb_eq in EQ2. subst. replace a0 with a1 in *.
      { rewrite Ascii.eqb_refl in EQ0. ss. }
      { eapply ascii_le_antisym; et. }
    }
    { eapply AsciiOrder.leb_trans; et. }
  Qed.

  Definition eqA: t -> t -> Prop := eq.

  Lemma eqb_eq : forall x y : t, eqA x y <-> leb x y = true /\ leb y x.
  Proof.
    i. split.
    { i. inv H. destruct (leb_total y y); auto. }
    { i. des. apply string_le_antisym; auto. }
  Qed.
End StringOrder.

Module ProdFstOrder (A: TotalOrderBool) (B: Typ) <: TotalOrderBool.
  Definition t := (A.t * B.t)%type.
  Definition leb := fun (x y: t) => A.leb (fst x) (fst y).
  Lemma leb_total : forall x y : t, leb x y = true \/ leb y x = true.
  Proof. i. eapply A.leb_total. Qed.

  Lemma leb_trans : Transitive leb.
  Proof. ii. eapply A.leb_trans; et. Qed.

  Definition eqA (x y: t) := A.eqA (fst x) (fst y).

  Lemma eqb_eq : forall x y : t, eqA x y <-> leb x y = true /\ leb y x.
  Proof.
    i. split.
    { i. destruct x, y. unfold eqA, leb in *. ss.
      eapply A.eqb_eq; auto. }
    { i. destruct x, y. unfold eqA, leb in *. ss.
      eapply A.eqb_eq; auto. }
  Qed.
End ProdFstOrder.

Require Import Sorting.Mergesort.
Require Import Sorting.Sorted.

Inductive NoDupA A (eqA: A -> A -> Prop) : list A -> Prop :=
| NoDupA_nil : NoDupA eqA []
| NoDupA_cons
    x l
    (HD: Forall (fun a => ~ eqA x a) l)
    (TL: NoDupA eqA l)
  :
    NoDupA eqA (x :: l)
.

Lemma NoDupA_eq_Nodup A (l: list A)
  :
    NoDupA eq l <-> NoDup l.
Proof.
  induction l.
  { split; i; econs. }
  split; i.
  { inv H. econs; et.
    { ii. eapply Forall_forall in HD; et. }
    { eapply IHl; et. }
  }
  { inv H. econs; et.
    { eapply Forall_forall. ii. subst. ss. }
    { eapply IHl; et. }
  }
Qed.

Lemma NoDupA_permutation A eqA
      (SYMM: Symmetric eqA)
      (l0 l1: list A)
      (PERM: Permutation l0 l1)
      (NODUP: NoDupA eqA l0)
  :
    NoDupA eqA l1.
Proof.
  induction PERM; et.
  { inv NODUP. econs; et.
    eapply Permutation_Forall; et. }
  { inv NODUP. inv TL. inv HD. econs; et.
    econs; et. }
Qed.

Lemma NoDupA_impl A eqA eqA'
      (IMPL: eqA' <2= eqA)
      (l: list A)
      (NODUP: NoDupA eqA l)
  :
    NoDupA eqA' l.
Proof.
  induction l; et.
  { econs. }
  { inv NODUP. econs; et. eapply Forall_impl; et.
    ii. eapply H; et. }
Qed.

Module OrderSort (A: TotalOrderBool).
  Include (Sort A).

  Lemma permutation_sorted_unique (l0 l1: list A.t)
        (PERM: Permutation l0 l1)
        (NODUP: NoDupA A.eqA l0)
        (SORTED0: StronglySorted A.leb l0)
        (SORTED1: StronglySorted A.leb l1)
    :
      l0 = l1.
  Proof.
    remember (length l0) as n.
    ginduction n; ii; ss.
    { destruct l0; ss. apply Permutation_nil in PERM; ss. }
    destruct l0; ss. clarify.
    destruct l1; ss.
    { sym in PERM. apply Permutation_nil_cons in PERM. ss. }
    destruct (classic (t = t0)).
    - subst.
      f_equal. eapply IHn; et.
      { eapply Permutation_cons_inv; et. }
      { inv NODUP; ss. }
      { eapply StronglySorted_inv; et. }
      { eapply StronglySorted_inv; et. }
    - exfalso.
      exploit Permutation_in.
      { eapply PERM. }
      { left; refl. }
      intro T.
      exploit Permutation_in.
      { sym. eapply PERM. }
      { left; refl. }
      intro U.
      ss. des; clarify.
      assert(EQ: A.eqA t t0).
      {
        inv SORTED0. inv SORTED1.
        rewrite Forall_forall in *.
        exploit H3; et. intro TT.
        exploit H5; et. intro UU.
        eapply A.eqb_eq; et.
      }
      inv NODUP.
      rewrite Forall_forall in *. exploit HD; et.
  Qed.

  Lemma sort_StronglySorted (l: list A.t)
    :
      StronglySorted A.leb (sort l).
  Proof.
    eapply StronglySorted_sort.
    eapply A.leb_trans.
  Qed.
End OrderSort.

Module AListSort (V: Typ).
  Module _Order := ProdFstOrder StringOrder V.
  Include (OrderSort _Order).

  Definition t := alist string V.t.

  Lemma sort_permutation (l: t)
    :
      Permutation l (sort l).
  Proof.
    eapply Permuted_sort.
  Qed.

  Lemma sort_add_comm (l0 l1: t)
        (ND: NoDup (List.map fst (l0 ++ l1)))
    :
      sort (l0 ++ l1) = sort (l1 ++ l0).
  Proof.
    eapply permutation_sorted_unique.
    { etrans.
      { symmetry. eapply sort_permutation. }
      etrans.
      { eapply Permutation_app_comm. }
      { eapply sort_permutation. }
    }
    { eapply NoDupA_permutation.
      { ii. eapply _Order.eqb_eq. eapply _Order.eqb_eq in H. des. auto. }
      { eapply sort_permutation. }
      revert ND. generalize (l0 ++ l1). clear. induction l.
      { i. econs. }
      { i. ss. inv ND. econs; et.
        eapply Forall_forall. ii. eapply H1.
        replace (fst a) with (fst x).
        eapply in_map. ss.
      }
    }
    { eapply sort_StronglySorted. }
    { eapply sort_StronglySorted. }
  Qed.
End AListSort.

Notation "f ∘ g" := (fun x => (f (g x))). (*** It is already in Coqlib but Coq seems to have a bug; it gets overriden by the one in program_scope in the files that import this file ***)
