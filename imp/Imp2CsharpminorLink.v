Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.
Require Import Imp2Csharpminor.
Require Import Imp2CsharpminorGenv.

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

  Definition name1 {A} {B} (l: list (A * B)) := List.map fst l.
  Definition name2 {A} {B} {C} (l: list (A * (B * C))) := List.map (fst ∘ snd) l.

  Variable src1 : Imp.programL.
  Variable src2 : Imp.programL.

  Definition l_nameL := src1.(nameL) ++ src2.(nameL).
  Definition l_pvs := src1.(prog_varsL) ++ src2.(prog_varsL).
  Definition l_pfs := src1.(prog_funsL) ++ src2.(prog_funsL).
  Definition l_publicL := src1.(publicL) ++ src2.(publicL).
  Definition l_defsL := src1.(defsL) ++ src2.(defsL).

  (* check defined names are unique *)
  Definition link_imp_cond1 := Coqlib.list_norepet_dec dec ((name1 l_pvs) ++ (name2 l_pfs)).

  Lemma link_imp_cond1_prop :
    forall (_LIC1: link_imp_cond1),
      <<LIC1: Coqlib.list_norepet ((name1 l_pvs) ++ (name2 l_pfs))>>.
  Proof.
    i. unfold link_imp_cond1 in *. apply sumbool_to_bool_true in _LIC1. ss.
  Qed.

  (* check external decls are consistent *)
  Definition link_imp_cond2 :=
    let sd := string_Dec in
    let c1 := Coqlib.list_norepet_dec dec (src1.(ext_varsL) ++ (name2 l_pfs)) in
    let c2 := Coqlib.list_norepet_dec dec (src2.(ext_varsL) ++ (name2 l_pfs)) in
    let c3 := Coqlib.list_norepet_dec dec ((name1 src1.(ext_funsL)) ++ (name1 l_pvs)) in
    let c4 := Coqlib.list_norepet_dec dec ((name1 src2.(ext_funsL)) ++ (name1 l_pvs)) in
    c1 && c2 && c3 && c4.

  Lemma link_imp_cond2_prop :
    forall (_LIC2: link_imp_cond2 = true),
      (<<EV1: Coqlib.list_norepet (src1.(ext_varsL) ++ (name2 l_pfs))>>) /\
      (<<EV2: Coqlib.list_norepet (src2.(ext_varsL) ++ (name2 l_pfs))>>) /\
      (<<EF1: Coqlib.list_norepet ((name1 src1.(ext_funsL)) ++ (name1 l_pvs))>>) /\
      (<<EF2: Coqlib.list_norepet ((name1 src2.(ext_funsL)) ++ (name1 l_pvs))>>).
  Proof.
    i. unfold link_imp_cond2 in _LIC2. bsimpl. des.
    apply sumbool_to_bool_true in _LIC2. apply sumbool_to_bool_true in _LIC3.
    apply sumbool_to_bool_true in _LIC1. apply sumbool_to_bool_true in _LIC0.
    eauto.
  Qed.

  (* check external fun decls' sig *)
  Fixpoint __link_imp_cond3 (p : string * nat) (l : extFuns) :=
    let '(name, n) := p in
    match l with
    | [] => true
    | (name2, n2) :: t =>
      if (eqb name name2 && negb (n =? n2)%nat) then false
      else __link_imp_cond3 p t
    end
  .

  Lemma __link_imp_cond3_prop :
    forall p (l : list (string * nat))
      (__LIC3: __link_imp_cond3 p l = true),
      <<__LIC3: forall a, ((In a l) /\ (fst a = fst p)) -> (snd a = snd p)>>.
  Proof.
    i. red. depgen p. depgen l. clear. induction l; ii; ss; clarify.
    { des. clarify. }
    des; clarify; ss.
    { destruct p; ss. destruct a0; ss. clarify. des_ifs. bsimpl. des; bsimpl; ss; clarify.
      { rewrite eqb_refl in Heq. clarify. }
      rewrite Nat.eqb_eq in Heq. ss. }
    destruct p. destruct a0. ss; clarify. destruct a. ss; clarify. des_ifs. bsimpl. des.
    { set (k0:=(s, n0)) in *. set (k:=(s, n)) in *. eapply IHl in __LIC3.
      { instantiate (1:=k0) in __LIC3. subst k; subst k0; ss; clarify. }
      split; auto. }
    rewrite Nat.eqb_eq in Heq. clarify. eapply IHl in __LIC3.
    { instantiate (1:= (s, n0)) in __LIC3. ss; clarify. }
    split; ss; eauto.
  Qed.

  Fixpoint _link_imp_cond3 l :=
    match l with
    | [] => true
    | h :: t =>
      if (__link_imp_cond3 h t) then _link_imp_cond3 t
      else false
    end
  .

  Lemma _link_imp_cond3_prop :
    forall (l : list (string * nat))
      (_LIC3: _link_imp_cond3 l = true),
      <<_LIC3: forall a b, ((In a l) /\ (In b l) /\ (fst a = fst b)) -> (snd a = snd b)>>.
  Proof.
    i. red. depgen l. clear. induction l; i; ss; clarify.
    { des; clarify. }
    des; ss; clarify.
    - des_ifs. eapply __link_imp_cond3_prop in Heq. eapply Heq; eauto.
    - des_ifs. eapply __link_imp_cond3_prop in Heq. sym; eapply Heq; eauto.
    - des_ifs. assert (TRUE: true = true); auto.
  Qed.

  Definition link_imp_cond3 := _link_imp_cond3 (src1.(ext_funsL) ++ src2.(ext_funsL)).

  Lemma link_imp_cond3_prop :
    forall (LIC3: link_imp_cond3 = true),
      <<LIC3P: forall a b, ((In a (src1.(ext_funsL) ++ src2.(ext_funsL))) /\ (In b (src1.(ext_funsL) ++ src2.(ext_funsL)))
                       /\ (fst a = fst b)) -> (snd a = snd b)>>.
  Proof.
    i. unfold link_imp_cond3 in LIC3. eapply _link_imp_cond3_prop in LIC3. auto.
  Qed.

  (* merge external decls; vars is simple, funs assumes cond3 is passed *)
  (* link external decls; need to remove defined names *)
  Definition l_evs :=
    let l_evs0 := nodup string_Dec (src1.(ext_varsL) ++ src2.(ext_varsL)) in
    let l_pvsn := name1 l_pvs in
    List.filter (fun s => negb (in_dec string_Dec s l_pvsn)) l_evs0.

  (* Lemma l_ext_vars_prop : *)

  Definition l_efs :=
    let l_efs0 := nodup extFun_Dec (src1.(ext_funsL) ++ src2.(ext_funsL)) in
    let l_pfsn := name2 l_pfs in
    List.filter (fun sn => negb (in_dec string_Dec (fst sn) l_pfsn)) l_efs0.

  (* Linker for Imp programs, follows Clight's link_prog as possible *)
  Definition link_imp : option Imp.programL :=
    if (link_imp_cond1 && link_imp_cond2 && link_imp_cond3 &&
        (Coqlib.list_norepet_dec dec ((l_evs) ++ (name1 l_efs) ++ (name1 l_pvs) ++ (name2 l_pfs))))
    then Some (mk_programL l_nameL l_evs l_efs l_pvs l_pfs l_publicL l_defsL)
    else None
  .

End LINK.



Section LINKPROPS.


  Lemma pre_compile_iFuns_props
        src pcs
        (PCS: pre_compile_iFuns src = Some pcs)
  :
    <<PCSDEFS: Forall2 (fun a b =>
                          let fn := fst a in
                          let f := snd a in
                          (s2p fn = fst b) /\
                          (exists cf, (pre_compile_function fn f = Some cf) /\ (Gfun (Internal cf) = snd b)))
                       src pcs>>.
  Proof.
    depgen pcs. induction src; i; ss; clarify.
    { unfold pre_compile_iFuns in PCS. des_ifs. }
    destruct pcs.
    { clear IHsrc. unfold pre_compile_iFuns in PCS. des_ifs. }
    rename a into src0, p into pcs0. econs 2.
    - unfold pre_compile_iFuns in PCS. des_ifs_safe. ss. inv f. des_ifs_safe. ss. split; auto.
      exists f. split; auto.
    - apply IHsrc. unfold pre_compile_iFuns in PCS. des_ifs_safe. inv f.
      unfold pre_compile_iFuns. des_ifs.
  Qed.

  Lemma pre_compile_iFuns_props2
        src pcs
        (PCSDEFS: Forall2 (fun a b =>
                             let fn := fst a in
                             let f := snd a in
                             (s2p fn = fst b) /\
                             (exists cf, (pre_compile_function fn f = Some cf) /\ (Gfun (Internal cf) = snd b)))
                          src pcs)
    :
      <<PCS: pre_compile_iFuns src = Some pcs>>.
  Proof.
    depgen pcs. induction src; i; ss; clarify.
    { inv PCSDEFS. ss. }
    destruct pcs.
    { inv PCSDEFS. }
    rename a into src0, p into pcs0. inv PCSDEFS. des. rename H0 into CF, H1 into GD, H2 into ID, H4 into FA2.
    unfold pre_compile_iFuns in *. des_ifs.
    - red. f_equal. rewrite List.map_map. ss. f_equal.
      2:{ apply IHsrc in FA2. inv FA2. rewrite List.map_map. ss. }
      destruct src0. ss. rewrite CF. destruct pcs0; ss; clarify.
    - exfalso. apply n. clear n. inv f; auto.
    - exfalso. apply n. clear n. econs 2; eauto. destruct src0; ss. rewrite CF. ss.
    - apply IHsrc in FA2. clarify.
  Qed.

  Lemma pre_compile_iFuns_cons
        s src p pcs
        (PCSCONS : pre_compile_iFuns (s :: src) = Some (p :: pcs))
  :
    (<<PCS: pre_compile_iFuns src = Some pcs>>).
  Proof.
    apply pre_compile_iFuns_props in PCSCONS. inv PCSCONS. apply pre_compile_iFuns_props2 in H4. auto.
  Qed.

  Lemma pre_compile_iFuns_names
        src pcs
        (PCS: pre_compile_iFuns src = Some pcs)
  :
    <<PCSNAMES: List.map (compose s2p fst) src = List.map fst pcs>>.
  Proof.
    hexploit pre_compile_iFuns_props; eauto. i. induction H; ss; eauto.
    red. des. f_equal; eauto. apply IHForall2. apply pre_compile_iFuns_props2 in H0. auto.
  Qed.

  Lemma pre_compile_link_two
        src1 src2 pcs1 pcs2
        (PCS1: pre_compile_iFuns (List.map snd (prog_funsL src1)) = Some pcs1)
        (PCS2: pre_compile_iFuns (List.map snd (prog_funsL src2)) = Some pcs2)
    :
      <<PCS12: pre_compile_iFuns (List.map snd (l_pfs src1 src2)) = Some (pcs1 ++ pcs2)>>.
  Proof.
    unfold l_pfs. rewrite map_app. red.
    match goal with
    | [ |- pre_compile_iFuns (?_fs1 ++ ?_fs2) = _ ] => set (fs1:=_fs1) in *; set (fs2:=_fs2) in *
    end.
    unfold pre_compile_iFuns in *. des_ifs; ss; clarify.
    { repeat f_equal. rewrite map_app. rewrite map_app. ss. }
    exfalso. apply n. clear n. rewrite map_app. apply Forall_app; eauto.
  Qed.

  Lemma link_then_unique_ids
        src1 pcs1 src2 pcs2
        (PCS1: pre_compile_iFuns (List.map snd (prog_funsL src1)) = Some pcs1)
        (PCS2: pre_compile_iFuns (List.map snd (prog_funsL src2)) = Some pcs2)
        (LINK : link_imp_cond1 src1 src2 && link_imp_cond2 src1 src2 && link_imp_cond3 src1 src2 = true)
        (NOREPET1 : Coqlib.list_norepet
                      (List.map fst (pcs2 ++ compile_eFuns (ext_funsL src2) ++
                                     compile_iVars (prog_varsL src2) ++ compile_eVars (ext_varsL src2))))
        (NOREPET2 : Coqlib.list_norepet
                      (List.map fst (pcs1 ++ compile_eFuns (ext_funsL src1) ++
                                     compile_iVars (prog_varsL src1) ++ compile_eVars (ext_varsL src1))))
    :
      (<<NPREPETL: Coqlib.list_norepet
                     (List.map fst
                               ((pcs1 ++ pcs2) ++
                                (compile_eFuns (l_efs src1 src2)) ++
                                (compile_iVars (l_pvs src1 src2)) ++
                                (compile_eVars (l_evs src1 src2))))>>).
  Proof.
  Admitted.

  Lemma link_then_some_gmap
        src1 pcs1 gm1 src2 pcs2 gm2 srcl
        (PCS1: pre_compile_iFuns (List.map snd (prog_funsL src1)) = Some pcs1)
        (GMAP1 : get_gmap src1 = Some gm1)
        (PCS2: pre_compile_iFuns (List.map snd (prog_funsL src2)) = Some pcs2)
        (GMAP2 : get_gmap src2 = Some gm2)
        (LINK : link_imp src1 src2 = Some srcl)
    :
      (<<GMAPL: get_gmap srcl =
                Some (mk_gmap (compile_eVars (l_evs src1 src2))
                              (compile_eFuns (l_efs src1 src2))
                              (compile_iVars (l_pvs src1 src2))
                              (pcs1 ++ pcs2))>>) /\
      (<<NPREPETL: Coqlib.list_norepet
                     (List.map fst
                               ((pcs1 ++ pcs2) ++
                                (compile_eFuns (l_efs src1 src2)) ++
                                (compile_iVars (l_pvs src1 src2)) ++
                                (compile_eVars (l_evs src1 src2))))>>).
  Proof.
    unfold link_imp in LINK. des_ifs. unfold get_gmap; ss. erewrite pre_compile_link_two; eauto.
    uo; ss. unfold get_gmap in *. des_ifs; ss.
    uo; des_ifs; ss; clarify. split.
    { exfalso. apply n; clear n. apply link_then_unique_ids; eauto. depgen Heq. clear. i. bsimpl. des. eauto. }
    apply link_then_unique_ids; eauto. depgen Heq; clear; i. bsimpl; des; eauto.
  Qed.

  Lemma ext_vars_names :
    forall src, <<EVN: List.map fst (compile_eVars (ext_varsL src)) = List.map s2p (ext_varsL src)>>.
  Proof.
    i. unfold compile_eVars. rewrite List.map_map. apply List.map_ext. i. ss.
  Qed.

  Lemma ext_funs_names :
    forall src, <<EFN: List.map fst (compile_eFuns (ext_funsL src)) = List.map (compose s2p fst) (ext_funsL src)>>.
  Proof.
    i. unfold compile_eFuns. rewrite List.map_map. apply List.map_ext. i. destruct a. ss.
  Qed.

  Lemma int_vars_names :
    forall src, <<IVN: List.map fst (compile_iVars (prog_varsL src)) = List.map (compose s2p fst) (prog_varsL src)>>.
  Proof.
    i. unfold compile_iVars. rewrite List.map_map. apply List.map_ext. i. destruct a; ss.
  Qed.

  Lemma int_funs_names :
    forall src pcs
      (PCS : pre_compile_iFuns (List.map snd (prog_funsL src)) = Some pcs),
      <<IFN: List.map fst pcs = List.map (compose s2p (compose fst snd)) (prog_funsL src)>>.
  Proof.
    i. unfold pre_compile_iFuns in PCS. des_ifs. rewrite List.map_map in f. do 3 rewrite List.map_map. red.
    apply map_ext_strong. i. apply List.Forall_map in f. rewrite Forall_forall in f. apply f in IN.
    des_ifs. ss. destruct x. ss. destruct p. clarify.
  Qed.



End LINKPROPS.





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
    - unfold wf_prog_perm in *; ss. unfold l_pvs; unfold l_pfs; unfold l_defsL.
      rewrite! map_app. red. rewrite <- app_assoc.
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
