Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.

From compcert Require Import AST Csharpminor Globalenvs Linking.

Set Implicit Arguments.

Definition extFun_Dec : forall x y : (string * nat), {x = y} + {x <> y}.
Proof.
  i. destruct x, y.
  assert (NC: {n = n0} + {n <> n0}); auto using nat_Dec.
  assert (SC: {s = s0} + {s <> s0}); auto using string_Dec.
  destruct NC; destruct SC; clarify; auto.
  all: right; intros p; apply pair_equal_spec in p; destruct p; clarify.
Qed.

Section LINK.

  Variable src1 : Imp.programL.
  Variable src2 : Imp.programL.

  Let l_nameL := src1.(nameL) ++ src2.(nameL).
  Let l_prog_varsL := src1.(prog_varsL) ++ src2.(prog_varsL).
  Let l_prog_funsLM := src1.(prog_funsL) ++ src2.(prog_funsL).
  Let l_prog_funsL := List.map snd l_prog_funsLM.
  Let l_publicL := src1.(publicL) ++ src2.(publicL).
  Let l_defsL := src1.(defsL) ++ src2.(defsL).

  Let check_name_unique1 {K} {A} {B} decK
      (l1 : list (K * A)) (l2 : list (K * B)) :=
    let l1_k := List.map fst l1 in
    let l2_k := List.map fst l2 in
    Coqlib.list_norepet_dec decK (l1_k ++ l2_k).

  (* check defined names are unique *)
  Definition link_imp_cond1 :=
    check_name_unique1 string_Dec l_prog_varsL l_prog_funsL.

  Let check_name_unique2 {K} {B} decK
      (l1 : list K) (l2 : list (K * B)) :=
    let l2_k := List.map fst l2 in
    Coqlib.list_norepet_dec decK (l1 ++ l2_k).

  (* check external decls are consistent *)
  Definition link_imp_cond2 :=
    let sd := string_Dec in
    let c1 := check_name_unique2 sd src1.(ext_varsL) l_prog_funsL in
    let c2 := check_name_unique2 sd src2.(ext_varsL) l_prog_funsL in
    let c3 := check_name_unique1 sd src1.(ext_funsL) l_prog_varsL in
    let c4 := check_name_unique1 sd src2.(ext_funsL) l_prog_varsL in
    c1 && c2 && c3 && c4.

  (* check external fun decls' sig *)
  Fixpoint _link_imp_cond3' (p : string * nat) (l : extFuns) :=
    let '(name, n) := p in
    match l with
    | [] => true
    | (name2, n2) :: t =>
      if (eqb name name2 && negb (n =? n2)%nat) then false
      else _link_imp_cond3' p t
    end
  .

  Fixpoint _link_imp_cond3 l :=
    match l with
    | [] => true
    | h :: t =>
      if (_link_imp_cond3' h t) then _link_imp_cond3 t
      else false
    end
  .

  Definition link_imp_cond3 :=
    _link_imp_cond3 (src1.(ext_funsL) ++ src2.(ext_funsL)).

  (* merge external decls; vars is simple, funs assumes cond3 is passed *)
  Let l_ext_vars0 := nodup string_Dec (src1.(ext_varsL) ++ src2.(ext_varsL)).

  Let l_ext_funs0 := nodup extFun_Dec (src1.(ext_funsL) ++ src2.(ext_funsL)).

  (* link external decls; need to remove defined names *)
  Let l_ext_vars :=
    let l_prog_varsL' := List.map fst l_prog_varsL in
    List.filter (fun s => negb (in_dec string_Dec s l_prog_varsL')) l_ext_vars0.

  Let l_ext_funs :=
    let l_prog_funsL' := List.map fst l_prog_funsL in
    List.filter (fun sn => negb (in_dec string_Dec (fst sn) l_prog_funsL')) l_ext_funs0.

  (* Linker for Imp programs, follows Clight's link_prog as possible *)
  Definition link_imp : option Imp.programL :=
    if (link_imp_cond1 && link_imp_cond2 && link_imp_cond3)
    then Some (mk_programL l_nameL l_ext_vars l_ext_funs l_prog_varsL l_prog_funsLM l_publicL l_defsL)
    else None
  .

End LINK.



Section LINKLIST.

  Definition fold_left_option {T} f (t : list T) (opth : option T) :=
    fold_left (fun opt s2 => match opt with | Some s1 => f s1 s2 | None => None end) t opth.

  Lemma fold_left_option_None {T} :
    forall f (l : list T), fold_left_option f l None = None.
  Proof.
    intros f. induction l; ss; clarify.
  Qed.

  Definition fold_right_option {T} f (opt : option T) (l : list T) :=
    fold_right (fun s2 o => match o with | Some s1 => f s2 o | None => None end) opt l.

  Definition fold_right_option_None {T} :
    forall f (l : list T), fold_right_option f None l = None.
  Proof.
    intros f. induction l; ss; clarify. rewrite IHl; ss.
  Qed.

  (* Definition link_imp_list src_list := *)
  (*   match src_list with *)
  (*   | [] => None *)
  (*   | src_h :: src_t => *)
  (*     fold_left_option link_imp src_t (Some src_h) *)
  (*   end. *)

  Fixpoint link_imp_list src_list :=
    match src_list with
    | [] => None
    | [a] => Some a
    | a :: l =>
      match link_imp_list l with None => None | Some b => link_imp a b end
    end.

  Definition link_imps (src_list: list Imp.program) := link_imp_list (List.map lift src_list).

End LINKLIST.





Section PROOF.

  Import Permutation.

  Definition wf_prog_perm (src: Imp.programL) :=
    <<WFPROG: Permutation
                ((List.map fst src.(prog_varsL)) ++ (List.map (compose fst snd) src.(prog_funsL)))
                (List.map fst src.(defsL))>>.

  Definition wf_prog_gvar (src: Imp.programL) :=
    <<WFPROG2 : forall gn gv, In (gn, Sk.Gvar gv) (Sk.sort (defsL src)) -> In (gn, gv) (prog_varsL src)>>.

  Definition wf_prog src := wf_prog_perm src /\ wf_prog_gvar src.

  Lemma lifted_then_wf :
    forall (src: Imp.program), <<WFLIFT: wf_prog (lift src)>>.
  Proof.
    i. unfold lift. split.
    - unfold wf_prog_perm. ss. unfold defs. rewrite map_app. rewrite! List.map_map. red. unfold compose. ss.
      match goal with
      | [ |- Permutation (?lv1 ++ ?lf1) (?lf2 ++ ?lv2)] => assert (FUNS: lf1 = lf2)
      end.
      { remember (prog_funs src) as l. clear Heql src. induction l; ss; clarify.
        rewrite IHl. f_equal. destruct a. ss. }
      match goal with
      | [ |- Permutation (?lv1 ++ ?lf1) (?lf2 ++ ?lv2)] => assert (VARS: lv1 = lv2)
      end.
      { remember (prog_vars src) as l. clear Heql FUNS src. induction l; ss; clarify.
        rewrite IHl. f_equal. destruct a. ss. }
      rewrite FUNS; clear FUNS. rewrite VARS; clear VARS. apply Permutation_app_comm.
    - unfold wf_prog_gvar. ss. red. unfold defs. i. apply Sk.sort_incl_rev in H.
      apply in_app_or in H. des.
      + apply Coqlib.list_in_map_inv in H. des. destruct x. ss.
      + apply Coqlib.list_in_map_inv in H. des. destruct x. clarify.
  Qed.

  Lemma linked_two_wf :
    forall (src1 src2: Imp.programL) srcl
      (WF1: wf_prog src1)
      (WF2: wf_prog src2)
      (LINKED: link_imp src1 src2 = Some srcl),
      <<WFLINK: wf_prog srcl>>.
  Proof.
    i. unfold wf_prog in *. des. unfold link_imp in LINKED. des_ifs. split.
    - unfold wf_prog_perm in *; ss. rewrite! map_app. red. rewrite <- app_assoc.
      match goal with
      | [ |- Permutation (?l1 ++ ?l2 ++ ?l3 ++ ?l4) _ ] =>
        cut (Permutation (l1 ++ l2 ++ l3 ++ l4) ((l1 ++ l3) ++ l2 ++ l4))
      end.
      { i. eapply Permutation_trans; eauto. apply Permutation_app; eauto. }
      clear. rewrite <- app_assoc. apply Permutation_app_head.
      rewrite! app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
    - unfold wf_prog_gvar in *; ss. ii. apply Sk.sort_incl_rev in H. apply in_or_app. apply in_app_or in H. des.
      + left; apply WF3. apply Sk.sort_incl. auto.
      + right; apply WF0. apply Sk.sort_incl. auto.
  Qed.

  Lemma linked_list_wf :
    forall (src_list: list Imp.programL) srcl
      (WFPROGS: Forall wf_prog src_list)
      (LINKED: link_imp_list src_list = Some srcl),
      <<WFLINK: wf_prog srcl>>.
  Proof.
    i. destruct src_list as [| src0 src_list]; ss; clarify.
    depgen src0. depgen srcl. induction src_list; i; ss; clarify.
    { inv WFPROGS. ss. }
    rename a into src1. des_ifs; ss; clarify.
    { inv WFPROGS. eapply IHsrc_list; ss; clarify; eauto. econs; eauto. inv H2. eapply (linked_two_wf H1 H3 LINKED). }
    rename l into src_list, p1 into src2, p into srct. des_ifs.
    { specialize IHsrc_list with srct src1. inv WFPROGS. apply IHsrc_list in H2; ss. eapply (linked_two_wf H1 H2 LINKED). }
    rename l into src_list. specialize IHsrc_list with srct src1. inv WFPROGS. hexploit IHsrc_list; eauto. i.
    eapply (linked_two_wf H1 H LINKED).
  Qed.

  Lemma linked_list_wf_lift :
    forall (src_list: list Imp.program) srcl
      (LINKED: link_imps src_list = Some srcl),
      <<WFLINK: wf_prog srcl>>.
  Proof.
    i. unfold link_imps in LINKED. assert (WFPROGS: Forall wf_prog (List.map lift src_list)).
    { clear LINKED. clear srcl. induction src_list; ss; clarify. econs; auto. apply lifted_then_wf. }
    hexploit linked_list_wf; eauto.
  Qed.

End PROOF.
