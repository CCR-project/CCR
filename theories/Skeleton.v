Require Import Coqlib.
Require Import Universe.
Require Import PCM.

Set Implicit Arguments.



Fixpoint _find_idx {A} (f: A -> bool) (l: list A) (acc: nat): option (nat * A) :=
  match l with
  | [] => None
  | hd :: tl => if (f hd) then Some (acc, hd) else _find_idx f tl (S acc)
  end
.

Definition find_idx {A} (f: A -> bool) (l: list A): option (nat * A) := _find_idx f l 0.

Notation "'do' ' X <- A ; B" := (o_bind A (fun _x => match _x with | X => B end))
                                  (at level 200, X pattern, A at level 100, B at level 200)
                                : o_monad_scope.

Lemma find_idx_red {A} (f: A -> bool) (l: list A):
  find_idx f l =
  match l with
  | [] => None
  | hd :: tl =>
    if (f hd)
    then Some (0, hd)
    else
      do (n, a) <- find_idx f tl;
      Some (S n, a)
  end.
Proof.
  unfold find_idx. generalize 0. induction l; ss.
  i. des_ifs; ss.
  - rewrite Heq0. ss.
  - rewrite Heq0. specialize (IHl (S n)). rewrite Heq0 in IHl. ss.
Qed.


Module SkEnv.

  Record t: Type := mk {
    blk2id: mblock -> option gname;
    id2blk: gname -> option mblock;
  }
  .

  Definition wf (ske: t): Prop :=
    forall id blk, ske.(id2blk) id = Some blk <-> ske.(blk2id) blk = Some id.

End SkEnv.






(* Require Import Logic.FinFun. *)
(* Definition finfun A B: Type := *)
(*   { f: A -> option B | *)
(*     exists (card: nat) (inj: A -> nat), *)
(*     Injective inj /\ forall a (IN: is_some (f a)), ((inj a) < card)%nat }. *)
(* Program Definition add_finfun A B (add: B -> B -> B) (f g: finfun A B): finfun A B := *)
(*   exist _ (fun a => match `f a, `g a with *)
(*                     | Some x, None => Some x *)
(*                     | None, Some y => Some y *)
(*                     | Some x, Some y => Some (add x y) *)
(*                     | None, None => None *)
(*                     end) _. *)
(* Next Obligation. *)
(*   destruct f, g; ss. des. *)
(*   exists (card + card0)%nat. eexists (fun a => if (is_some (x a)) && (inj a <? card)%nat *)
(*                                                then inj a *)
(*                                                else (card + (inj0 a))%nat). *)
(*   esplits; eauto. *)
(*   - rr. ii. des_ifs; bsimpl; des; apply_all_once Nat.leb_le; apply_all_once Nat.leb_gt; *)
(*               apply_all_once e; apply_all_once e0; clarify; *)
(*               apply_all_once e1; apply_all_once e2; clarify. *)
(* Qed. *)



Require Import Orders.

Module Sk.

  Inductive gdef: Type := Gfun | Gvar (gv: Z).

  Definition t: Type := alist gname gdef.

  Definition unit: t := nil.

  Definition add: t -> t -> t := @List.app _.

  Definition wf (sk: t): Prop := @List.NoDup _ (List.map fst sk).

  Module GDef <: Typ. Definition t := gdef. End GDef.
  Module SkSort := AListSort GDef.

  Definition sort: t -> t := SkSort.sort.

  Definition sort_add_comm sk0 sk1
             (WF: wf (add sk0 sk1))
    :
      sort (add sk0 sk1) = sort (add sk1 sk0).
  Proof.
    eapply SkSort.sort_add_comm. eapply WF.
  Qed.

  Definition sort_wf sk (WF: wf sk):
    wf (sort sk).
  Proof.
    eapply Permutation.Permutation_NoDup; [|apply WF].
    eapply Permutation.Permutation_map.
    eapply SkSort.sort_permutation.
  Qed.

  (*** TODO: It might be nice if Sk.t also constitutes a resource algebra ***)
  (*** At the moment, List.app is not assoc/commutative. We need to equip RA with custom equiv. ***)

  Definition load_mem (sk: t): Mem.t :=
    Mem.mk
      (fun blk ofs =>
         do '(_, gd) <- (List.nth_error sk blk);
         match gd with
         | Gfun =>
           None
         | Gvar gv =>
           if (dec ofs 0%Z) then Some (Vint gv) else None
         end)
      (*** TODO: This simplified model doesn't allow function pointer comparsion.
           To be more faithful, we need to migrate the notion of "permission" from CompCert.
           CompCert expresses it with "nonempty" permission.
       ***)
      (*** TODO: When doing so, I would like to extend val with "Vfid (id: gname)" case.
           That way, I might be able to support more higher-order features (overriding, newly allocating function)
       ***)
      (List.length sk)
  .

  Definition load_skenv (sk: t): (SkEnv.t) :=
    let n := List.length sk in
    {|
      SkEnv.blk2id := fun blk => do '(gn, _) <- (List.nth_error sk blk); Some gn;
      SkEnv.id2blk := fun id => do '(blk, _) <- find_idx (fun '(id', _) => string_dec id id') sk; Some blk
    |}
  .

  Lemma load_skenv_wf
        sk
        (WF: wf sk)
    :
      <<WF: SkEnv.wf (load_skenv sk)>>
  .
  Proof.
    r in WF.
    rr. split; i; ss.
    - uo; des_ifs.
      + f_equal. ginduction sk; ss. i. inv WF.
        rewrite find_idx_red in Heq1. des_ifs; ss.
        { des_sumbool. subst. ss. clarify. }
        des_sumbool. uo. des_ifs. destruct p. ss.
        hexploit IHsk; et.
      + exfalso. ginduction sk; ss. i. inv WF.
        rewrite find_idx_red in Heq2. des_ifs; ss.
        des_sumbool. uo. des_ifs. destruct p. ss.
        hexploit IHsk; et.
    - ginduction sk; ss.
      { i. uo. ss. destruct blk; ss. }
      i. destruct a. inv WF. uo. destruct blk; ss; clarify.
      {  rewrite find_idx_red. uo. des_ifs; des_sumbool; ss. }
      hexploit IHsk; et. i.
      rewrite find_idx_red. uo. des_ifs; des_sumbool; ss. exfalso.
      subst. clear - Heq1 H2. ginduction sk; ss. i.
      rewrite find_idx_red in Heq1. des_ifs; des_sumbool; ss; et.
      uo. des_ifs. destruct p. eapply IHsk; et.
  Qed.

  Definition incl (sk0 sk1: Sk.t): Prop :=
    forall gn gd (IN: List.In (gn, gd) sk0),
      List.In (gn, gd) sk1.

  Program Instance incl_PreOrder: PreOrder incl.
  Next Obligation.
  Proof.
    ii. ss.
  Qed.
  Next Obligation.
  Proof.
    ii. eapply H0. eapply H. ss.
  Qed.

  Lemma sort_incl sk
    :
      incl sk (sort sk).
  Proof.
    ii. eapply Permutation.Permutation_in; [|apply IN].
    eapply SkSort.sort_permutation.
  Qed.

  Lemma sort_incl_rev sk
    :
      incl (sort sk) sk.
  Proof.
    ii. eapply Permutation.Permutation_in; [|apply IN].
    symmetry. eapply SkSort.sort_permutation.
  Qed.

  Definition incl_env (sk0: Sk.t) (skenv: SkEnv.t): Prop :=
    forall gn gd (IN: List.In (gn, gd) sk0),
    exists blk, <<FIND: skenv.(SkEnv.id2blk) gn = Some blk>>.

  Lemma incl_incl_env sk0 sk1
        (INCL: incl sk0 sk1)
    :
      incl_env sk0 (load_skenv sk1).
  Proof.
    ii. exploit INCL; et. i. ss. uo. des_ifs; et.
    exfalso. clear - x Heq0. ginduction sk1; et.
    i. ss. rewrite find_idx_red in Heq0. des_ifs.
    des_sumbool. uo.  des_ifs. des; clarify.
    eapply IHsk1; et.
  Qed.

  Lemma in_env_in_sk :
    forall sk blk symb,
      (<<FOUND: SkEnv.blk2id (Sk.load_skenv sk) blk = Some symb>>
       <->
       <<IN: exists def, In (symb, def) sk>>).
  Proof.
    admit "ez".
  Qed.
  
End Sk.

Coercion Sk.load_skenv: Sk.t >-> SkEnv.t.
Global Opaque Sk.load_skenv.
