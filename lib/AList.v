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


Global Instance function_Map (K V: Type) (dec: forall k0 k1, {k0=k1} + {k0<>k1}): (Map K V (K -> option V)) :=
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

Section ALIST.
  Lemma alist_find_some V (k: string) (l: alist string V) (v: V)
        (FIND: alist_find k l = Some v)
  :
    In (k, v) l.
  Proof.
    admit "ez".
  Qed.

  Lemma alist_find_none K `{Dec K} V (k: K) (l: alist K V)
        (FIND: alist_find k l = None)
        v
    :
      ~ In (k, v) l.
  Proof.
    admit "ez".
  Qed.

  Lemma alist_find_app K `{Dec K} V (k: K) (l0 l1: alist K V) (v: V)
        (FIND: alist_find k l0 = Some v)
    :
      alist_find k (l0 ++ l1) = Some v.
  Proof.
    admit "ez".
  Qed.

  Lemma alist_find_map K `{Dec K} V0 V1 (f: V0 -> V1) (k: K) (l: alist K V0)
    :
      alist_find k (List.map (fun '(k, v) => (k, f v)) l) = o_map (alist_find k l) f.
  Proof.
    admit "ez".
  Qed.
End ALIST.


Tactic Notation "asimpl" "in" ident(H) :=
  (try unfold alist_remove, alist_add in H); simpl in H.

Tactic Notation "asimpl" "in" "*" :=
  (try unfold alist_remove, alist_add in *); simpl in *.

Tactic Notation "asimpl" :=
  (try unfold alist_remove, alist_add); simpl.
