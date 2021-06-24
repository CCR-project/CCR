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

Import Permutation.

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

  (* (if/if) (if/iv) (if/ef) (if/ev) |
     (iv/if) (iv/iv) (iv/ef) (iv/ev) |
     (ef/if) (ef/iv) (ef/ef) (ef/ev) |
     (ev/if) (ev/iv) (ev/ef) 16.(ev/ev) 
  *)

  (* check external decls are consistent *)
  (* 13.ev/if, 4.if/ev, 10.ef/iv, 7.iv/ef, 15.ev/ef, 12.ef/ev *)
  Definition link_imp_cond1 :=
    let sd := string_Dec in
    let c1 := Coqlib.list_norepet_dec dec (src1.(ext_varsL) ++ (name2 l_pfs)) in
    let c2 := Coqlib.list_norepet_dec dec (src2.(ext_varsL) ++ (name2 l_pfs)) in
    let c3 := Coqlib.list_norepet_dec dec ((name1 src1.(ext_funsL)) ++ (name1 l_pvs)) in
    let c4 := Coqlib.list_norepet_dec dec ((name1 src2.(ext_funsL)) ++ (name1 l_pvs)) in
    let c5 := Coqlib.list_norepet_dec dec (src1.(ext_varsL) ++ (name1 src2.(ext_funsL))) in
    let c6 := Coqlib.list_norepet_dec dec (src2.(ext_varsL) ++ (name1 src1.(ext_funsL))) in
    c1 && c2 && c3 && c4 && c5 && c6.

  Lemma link_imp_cond1_prop :
    forall (_LIC2: link_imp_cond1 = true),
      (<<EV1: Coqlib.list_norepet (src1.(ext_varsL) ++ (name2 l_pfs))>>) /\
      (<<EV2: Coqlib.list_norepet (src2.(ext_varsL) ++ (name2 l_pfs))>>) /\
      (<<EF1: Coqlib.list_norepet ((name1 src1.(ext_funsL)) ++ (name1 l_pvs))>>) /\
      (<<EF1: Coqlib.list_norepet ((name1 src2.(ext_funsL)) ++ (name1 l_pvs))>>) /\
      (<<EVF1: Coqlib.list_norepet (src1.(ext_varsL) ++ (name1 src2.(ext_funsL)))>>) /\
      (<<EVF2: Coqlib.list_norepet (src2.(ext_varsL) ++ (name1 src1.(ext_funsL)))>>).
  Proof.
    i. unfold link_imp_cond1 in _LIC2. bsimpl. des.
    apply sumbool_to_bool_true in _LIC2. apply sumbool_to_bool_true in _LIC3.
    apply sumbool_to_bool_true in _LIC1. apply sumbool_to_bool_true in _LIC0.
    apply sumbool_to_bool_true in _LIC5. apply sumbool_to_bool_true in _LIC4.
    repeat split; eauto.
  Qed.

  (* check external fun decls' sig *)
  Fixpoint __link_imp_cond2 (p : string * nat) (l : extFuns) :=
    let '(id, n) := p in
    match l with
    | [] => true
    | (id2, n2) :: t =>
      if (eqb id id2 && negb (n =? n2)%nat) then false
      else __link_imp_cond2 p t
    end
  .

  Lemma __link_imp_cond2_prop :
    forall p (l : list (string * nat))
      (__LIC3: __link_imp_cond2 p l = true),
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

  Lemma __link_imp_cond2_prop_perm :
    forall p (l1 l2 : list (string * nat))
      (PERM: Permutation l1 l2)
      (__LIC3: __link_imp_cond2 p l1 = true),
      <<_LIC3: __link_imp_cond2 p l2 = true>>.
  Proof.
    i. red. depgen PERM. depgen __LIC3. clear. i. depgen p. induction PERM; i; ss; clarify.
    - destruct p; ss; clarify. destruct x; ss; clarify. des_ifs. eauto.
    - destruct p; ss; clarify. destruct x; ss; clarify. destruct y; ss; clarify. des_ifs.
    - eauto.
  Qed.

  Fixpoint _link_imp_cond2 l :=
    match l with
    | [] => true
    | h :: t =>
      if (__link_imp_cond2 h t) then _link_imp_cond2 t
      else false
    end
  .

  Lemma _link_imp_cond2_prop :
    forall (l : list (string * nat))
      (_LIC3: _link_imp_cond2 l = true),
      <<_LIC3: forall a b, ((In a l) /\ (In b l) /\ (fst a = fst b)) -> (snd a = snd b)>>.
  Proof.
    i. red. depgen l. clear. induction l; i; ss; clarify.
    { des; clarify. }
    des; ss; clarify.
    - des_ifs. eapply __link_imp_cond2_prop in Heq. eapply Heq; eauto.
    - des_ifs. eapply __link_imp_cond2_prop in Heq. sym; eapply Heq; eauto.
    - des_ifs. assert (TRUE: true = true); auto.
  Qed.

  Lemma _link_imp_cond2_prop_perm :
    forall (l1 l2 : list (string * nat))
      (PERM: Permutation l1 l2)
      (_LIC3: _link_imp_cond2 l1 = true),
      <<_LIC3: _link_imp_cond2 l2 = true>>.
  Proof.
    i. red. clear src1 src2. depgen _LIC3. induction PERM; i; ss; clarify.
    - des_ifs.
      + eauto.
      + hexploit __link_imp_cond2_prop_perm; eauto.
    - destruct x; destruct y; ss; clarify. des_ifs. bsimpl. des.
      + rewrite eqb_eq in Heq0. rewrite eqb_neq in Heq3. clarify.
      + rewrite Nat.eqb_eq in Heq3. rewrite Nat.eqb_neq in Heq4. clarify.
    - eauto.
  Qed.

  (* 11.ef/ef *)
  Definition link_imp_cond2 := _link_imp_cond2 (src1.(ext_funsL) ++ src2.(ext_funsL)).

  Lemma link_imp_cond2_prop :
    forall (LIC3: link_imp_cond2 = true),
      <<LIC3P: forall a b, ((In a (src1.(ext_funsL) ++ src2.(ext_funsL))) /\ (In b (src1.(ext_funsL) ++ src2.(ext_funsL)))
                       /\ (fst a = fst b)) -> (snd a = snd b)>>.
  Proof.
    i. unfold link_imp_cond2 in LIC3. eapply _link_imp_cond2_prop in LIC3. auto.
  Qed.

  (* merge external decls; vars is simple, funs assumes cond2 is passed *)
  (* link external decls; need to remove defined names *)

  (* 8.iv/ev, 14.ev/iv *)
  Definition l_evs :=
    let l_evs0 := nodup string_Dec (src1.(ext_varsL) ++ src2.(ext_varsL)) in
    let l_pvsn := name1 l_pvs in
    List.filter (fun s => negb (in_dec string_Dec s l_pvsn)) l_evs0.

  (* 3.if/ef, 9.ef/if *)
  Definition l_efs :=
    let l_efs0 := nodup extFun_Dec (src1.(ext_funsL) ++ src2.(ext_funsL)) in
    let l_pfsn := name2 l_pfs in
    List.filter (fun sn => negb (in_dec string_Dec (fst sn) l_pfsn)) l_efs0.

  (* check names are unique *)
  Definition link_imp_cond3 :=
    Coqlib.list_norepet_dec dec ((name1 init_g0) ++ (name1 syscalls) ++
                                 (name1 l_efs) ++ (l_evs) ++ (name2 l_pfs) ++ (name1 l_pvs)).

  Lemma link_imp_cond3_prop :
    forall (_LIC3: link_imp_cond3),
    <<LIC3: Coqlib.list_norepet ((name1 init_g0) ++ (name1 syscalls) ++
                                 (name1 l_efs) ++ (l_evs) ++ (name2 l_pfs) ++ (name1 l_pvs))>>.
  Proof.
    i. unfold link_imp_cond3 in *. apply sumbool_to_bool_true in _LIC3. ss.
  Qed.

  Lemma _link_imp_cond3_ints :
    forall (_LIC3: link_imp_cond3),
      <<INTS: Coqlib.list_norepet ((name2 (prog_funsL src1)) ++ (name2 (prog_funsL src2)) ++
                                   (name1 (prog_varsL src1)) ++ (name1 (prog_varsL src2)))>>.
  Proof.
    ii. red. apply link_imp_cond3_prop in _LIC3. des.
    do 4 (apply Coqlib.list_norepet_append_right in _LIC3).
    unfold l_pfs in _LIC3; unfold l_pvs in _LIC3. unfold name2 in *; unfold name1 in *.
    rewrite ! map_app in _LIC3. rewrite <- app_assoc in _LIC3. auto.
  Qed.

  (* 1.if/if, 2.if/iv, 5.iv/if, 6.iv/iv *)
  Lemma link_imp_cond3_ints :
    forall (_LIC3: link_imp_cond3),
      (<<IFIF: Coqlib.list_disjoint (name2 (prog_funsL src1)) (name2 (prog_funsL src2))>>) /\
      (<<IFIV: Coqlib.list_disjoint (name2 (prog_funsL src1)) (name1 (prog_varsL src2))>>) /\
      (<<IVIF: Coqlib.list_disjoint (name1 (prog_varsL src1)) (name2 (prog_funsL src2))>>) /\
      (<<IVIV: Coqlib.list_disjoint (name1 (prog_varsL src1)) (name1 (prog_varsL src2))>>).
  Proof.
    i. apply _link_imp_cond3_ints in _LIC3. des.
    apply Coqlib.list_norepet_app in _LIC3. des.
    repeat split.
    { unfold Coqlib.list_disjoint in *. ii. hexploit _LIC1. eapply H.
      { apply in_app_iff. left; eauto. }
      ii. clarify. }
    { unfold Coqlib.list_disjoint in *. ii. hexploit _LIC1. eapply H.
      { apply in_app_iff. right. apply in_app_iff; right. eauto. }
      ii. clarify. }
    all: clear _LIC1 _LIC3.
    all: apply Coqlib.list_norepet_app in _LIC0; des.
    { clear _LIC0 _LIC1. unfold Coqlib.list_disjoint in *. ii. hexploit _LIC2. eapply H0.
      { apply in_app_iff. left. eapply H. }
      ii. clarify. }
    clear _LIC0 _LIC2. apply Coqlib.list_norepet_app in _LIC1. des.
    unfold Coqlib.list_disjoint in *. ii. hexploit _LIC2; eauto.
  Qed.

  (* Linker for Imp programs *)
  Definition link_imp : option Imp.programL :=
    if (link_imp_cond1 && link_imp_cond2 && link_imp_cond3)
    then Some (mk_programL l_nameL l_evs l_efs l_pvs l_pfs l_publicL l_defsL)
    else None
  .

End LINK.





Section DECOMP.

  Lemma ext_vars_names :
    forall src, <<EVN: List.map fst (compile_eVars (ext_varsL src)) = List.map s2p (ext_varsL src)>>.
  Proof.
    i. unfold compile_eVars. rewrite List.map_map. apply List.map_ext. i. ss.
  Qed.

  Lemma ext_funs_names :
    forall src, <<EFN: List.map fst (compile_eFuns (ext_funsL src)) = List.map (s2p ∘ fst) (ext_funsL src)>>.
  Proof.
    i. unfold compile_eFuns. rewrite List.map_map. apply List.map_ext. i. destruct a. ss.
  Qed.

  Lemma int_vars_names :
    forall src, <<IVN: List.map fst (compile_iVars (prog_varsL src)) = List.map (s2p ∘ fst) (prog_varsL src)>>.
  Proof.
    i. unfold compile_iVars. rewrite List.map_map. apply List.map_ext. i. destruct a; ss.
  Qed.

  Lemma int_funs_names :
    forall src, <<IFN: List.map fst (compile_iFuns (prog_funsL src)) = List.map (s2p ∘ (fst ∘ snd)) (prog_funsL src)>>.
  Proof.
    i. unfold compile_iFuns. rewrite List.map_map. apply List.map_ext. i. destruct a. destruct p. ss.
  Qed.

  Lemma decomp_init_g :
    forall id gd (INTGT: In (id, gd) init_g),
      (<<MALLOC: (id = s2p "malloc") /\ (gd = Gfun (External EF_malloc))>>) \/
      (<<FREE: (id = s2p "free") /\ (gd = Gfun (External EF_free))>>).
  Proof.
    Local Transparent init_g. Local Transparent init_g0.
    i. unfold init_g in INTGT. unfold init_g0 in INTGT. ss. des; clarify; eauto.
    Local Opaque init_g0. Local Opaque init_g.
  Qed.

  Lemma decomp_c_sys :
    forall id gd (INTGT: In (id, gd) c_sys),
      (<<SYS: exists fd, (compile_eFun fd = (id, gd)) /\ (In fd syscalls)>>).
  Proof.
    i. unfold c_sys in INTGT. eapply Coqlib.list_in_map_inv in INTGT. des. exists x; eauto.
  Qed.

  Lemma decomp_efs :
    forall src id gd (INTGT: In (id, gd) (compile_eFuns (ext_funsL src))),
      (<<EFS: exists fd, (compile_eFun fd = (id, gd)) /\ (In fd (ext_funsL src))>>).
  Proof.
    i. unfold compile_eFuns in INTGT. eapply Coqlib.list_in_map_inv in INTGT. des. exists x; eauto.
  Qed.

  Lemma decomp_evs :
    forall src id gd (INTGT: In (id, gd) (compile_eVars (ext_varsL src))),
      (<<EVS: exists vd, (compile_eVar vd = (id, gd)) /\ (In vd (ext_varsL src))>>).
  Proof.
    i. unfold compile_eVars in INTGT. eapply Coqlib.list_in_map_inv in INTGT. des. exists x; eauto.
  Qed.

  Lemma decomp_ifs :
    forall src id gd (INTGT: In (id, gd) (compile_iFuns (prog_funsL src))),
      (<<IFS: exists fd, (compile_iFun fd = (id, gd)) /\ (In fd (prog_funsL src))>>).
  Proof.
    i. unfold compile_iFuns in INTGT. eapply Coqlib.list_in_map_inv in INTGT. des. exists x; eauto.
  Qed.

  Lemma decomp_ivs :
    forall src id gd (INTGT: In (id, gd) (compile_iVars (prog_varsL src))),
      (<<IVS: exists vd, (compile_iVar vd = (id, gd)) /\ (In vd (prog_varsL src))>>).
  Proof.
    i. unfold compile_iVars in INTGT. eapply Coqlib.list_in_map_inv in INTGT. des. exists x; eauto.
  Qed.

  Lemma decomp_gdefs :
    forall src id gd (INTGT : In (id, gd) (compile_gdefs src)),
      (<<MALLOC: (id = s2p "malloc") /\ (gd = Gfun (External EF_malloc))>>) \/
      (<<FREE: (id = s2p "free") /\ (gd = Gfun (External EF_free))>>) \/
      (<<SYS: exists fd, (compile_eFun fd = (id, gd)) /\ (In fd syscalls)>>) \/
      (<<EFS: exists fd, (compile_eFun fd = (id, gd)) /\ (In fd (ext_funsL src))>>) \/
      (<<EVS: exists vd, (compile_eVar vd = (id, gd)) /\ (In vd (ext_varsL src))>>) \/
      (<<IFS: exists fd, (compile_iFun fd = (id, gd)) /\ (In fd (prog_funsL src))>>) \/
      (<<IVS: exists vd, (compile_iVar vd = (id, gd)) /\ (In vd (prog_varsL src))>>).
  Proof.
    i. unfold compile_gdefs in INTGT.
    apply in_app_or in INTGT. des.
    { apply decomp_init_g in INTGT. des; auto. }
    apply in_app_or in INTGT. des.
    { apply decomp_c_sys in INTGT. auto. }
    apply in_app_or in INTGT. des.
    { apply decomp_efs in INTGT. auto. }
    apply in_app_or in INTGT. des.
    { apply decomp_evs in INTGT. do 4 right. left. auto. }
    apply in_app_or in INTGT. des.
    { apply decomp_ifs in INTGT. do 5 right. auto. }
    apply decomp_ivs in INTGT. do 6 right. auto.
  Qed.

  Lemma has_malloc :
    forall src, (<<MALLOC: In (s2p "malloc", Gfun (External EF_malloc)) (compile_gdefs src)>>).
  Proof.
    i. unfold compile_gdefs. apply in_or_app. left.
    Local Transparent init_g. Local Transparent init_g0.
    unfold init_g. unfold init_g0. ss. left; ss.
    Local Opaque init_g0. Local Opaque init_g.
  Qed.

  Lemma has_free :
    forall src, (<<FREE: In (s2p "free", Gfun (External EF_free)) (compile_gdefs src)>>).
  Proof.
    i. unfold compile_gdefs. apply in_or_app. left.
    Local Transparent init_g. Local Transparent init_g0.
    unfold init_g. unfold init_g0. ss. right; left; ss.
    Local Opaque init_g0. Local Opaque init_g.
  Qed.

  Lemma norepet_unique {A} {B} :
    forall (l : list (A * B)) id gd1 gd2
      (NOREPET : Coqlib.list_norepet (List.map fst l))
      (IN1: In (id, gd1) l)
      (IN2: In (id, gd2) l),
      gd1 = gd2.
  Proof.
    induction l; i; ss; clarify.
    des; ss; clarify.
    - inv NOREPET. apply (in_map fst) in IN1. ss.
    - inv NOREPET. apply (in_map fst) in IN2. ss.
    - inv NOREPET. destruct a; ss. eapply IHl; eauto.
  Qed.

  Lemma compile_gdefs_unique_defs :
    forall src id gd1 gd2
      (NOREPET : Coqlib.list_norepet (List.map fst (compile_gdefs src)))
      (IN1: In (id, gd1) (compile_gdefs src))
      (IN2: In (id, gd2) (compile_gdefs src)),
      gd1 = gd2.
  Proof. i. eapply norepet_unique; eauto. Qed.

End DECOMP.



Section SOLVEID.

  Lemma compile_gdefs_preserves_names :
    forall src,
      <<NAMES:
        List.map s2p
          ((name1 init_g0) ++ (name1 syscalls) ++
           (name1 src.(ext_funsL)) ++ src.(ext_varsL) ++ (name2 src.(prog_funsL)) ++ (name1 src.(prog_varsL)))
        =
        name1 (compile_gdefs src)>>.
  Proof.
    i. unfold compile_gdefs. red. unfold name1. repeat rewrite map_app. repeat f_equal.
    - sym. rewrite List.map_map. apply ext_funs_names.
    - sym. apply ext_vars_names.
    - sym. unfold name2. rewrite List.map_map. apply int_funs_names.
    - sym. rewrite List.map_map. apply int_vars_names.
  Qed.

  Lemma unique_gdefs_unique_name :
    forall src
      (NOREPET : Coqlib.list_norepet (name1 (compile_gdefs src))),
      <<NOREPET: Coqlib.list_norepet ((name1 src.(ext_funsL)) ++ src.(ext_varsL) ++
                                      (name2 src.(prog_funsL)) ++ (name1 src.(prog_varsL)))>>.
  Proof.
    i. rewrite <- compile_gdefs_preserves_names in NOREPET. repeat (rewrite map_app in NOREPET).
    do 2 apply Coqlib.list_norepet_append_right in NOREPET. red.
    rewrite NoDup_norepeat in *.
    repeat (rewrite <- map_app in NOREPET). apply NoDup_map_inv in NOREPET. ss.
  Qed.

  Lemma malloc_unique :
    forall src (NOREPET : Coqlib.list_norepet (List.map fst (compile_gdefs src))),
      ~ In (s2p "malloc") (name1 (c_sys ++ (compile_eFuns (ext_funsL src)) ++ (compile_eVars (ext_varsL src) ++
                                           (compile_iFuns (prog_funsL src)) ++ (compile_iVars (prog_varsL src))))).
  Proof.
    i. unfold compile_gdefs in NOREPET.
    Local Transparent init_g. Local Transparent init_g0.
    unfold init_g in NOREPET. unfold init_g0 in NOREPET. ss.
    Local Opaque init_g0. Local Opaque init_g.
    inv NOREPET. ss. eauto.
  Qed.

  Lemma free_unique :
    forall src (NOREPET : Coqlib.list_norepet (List.map fst (compile_gdefs src))),
      ~ In (s2p "free") (name1 (c_sys ++ (compile_eFuns (ext_funsL src)) ++ (compile_eVars (ext_varsL src) ++
                                         (compile_iFuns (prog_funsL src)) ++ (compile_iVars (prog_varsL src))))).
  Proof.
    i. unfold compile_gdefs in NOREPET.
    Local Transparent init_g. Local Transparent init_g0.
    unfold init_g in NOREPET. unfold init_g0 in NOREPET. ss.
    Local Opaque init_g0. Local Opaque init_g.
    inv NOREPET. inv H2. ss.
  Qed.

  Lemma syscalls_unique :
    forall src id
      (NOREPET : Coqlib.list_norepet (List.map fst (compile_gdefs src)))
      (SYS: In id (name1 c_sys)),
      ~ In id (name1 (init_g ++ (compile_eFuns (ext_funsL src)) ++ (compile_eVars (ext_varsL src) ++
                                (compile_iFuns (prog_funsL src)) ++ (compile_iVars (prog_varsL src))))).
  Proof.
    ii. unfold compile_gdefs in NOREPET.
    rewrite map_app in NOREPET. apply Coqlib.list_norepet_app in NOREPET. des.
    unfold name1 in H. rewrite map_app in H. apply in_app_or in H. des.
    { unfold Coqlib.list_disjoint in NOREPET1. hexploit NOREPET1; eauto.
      rewrite map_app. apply in_or_app. left; auto. }
    clear NOREPET NOREPET1.
    rewrite map_app in NOREPET0. apply Coqlib.list_norepet_app in NOREPET0. des. clear NOREPET0 NOREPET1.
    unfold Coqlib.list_disjoint in NOREPET2. ii. hexploit NOREPET2; eauto.
  Qed.

  Lemma l_efs_prop :
    forall src1 src2 name sig
      (NOREPET1 : Coqlib.list_norepet (name1 (ext_funsL src1) ++ ext_varsL src1 ++
                                       name2 (prog_funsL src1) ++ name1 (prog_varsL src1)))
      (NOREPET2 : Coqlib.list_norepet (name1 (ext_funsL src2) ++ ext_varsL src2 ++
                                       name2 (prog_funsL src2) ++ name1 (prog_varsL src2)))
      (IN1 : In (name, sig) (ext_funsL src1))
      (IN2 : In (name, sig) (ext_funsL src2)),
      <<INLEFS: In (compile_eFun (name, sig)) (compile_eFuns (l_efs src1 src2))>>.
  Proof.
    ii. red. unfold l_efs, compile_eFuns. apply in_map. apply filter_In. split.
    2:{ unfold name2, l_pfs. apply negb_true_iff. apply sumbool_to_bool_is_false. ii. ss.
        rewrite map_app in H. apply in_app_iff in H. des.
        - depgen src1. clear; i. apply (in_map fst) in IN1. ss. rewrite Coqlib.list_norepet_app in NOREPET1. des.
          clear NOREPET1 NOREPET0. unfold Coqlib.list_disjoint in NOREPET2. hexploit NOREPET2.
          { eauto. }
          { rewrite in_app_iff. right. rewrite in_app_iff; left. eauto. }
          ii. clarify.
        - depgen src2. clear; i. apply (in_map fst) in IN2. ss. rewrite Coqlib.list_norepet_app in NOREPET2. des.
          clear NOREPET2 NOREPET0. unfold Coqlib.list_disjoint in NOREPET1. hexploit NOREPET1.
          { eauto. }
          { rewrite in_app_iff. right. rewrite in_app_iff; left. eauto. }
          ii. clarify.
    }
    set (ef:=(name, sig)) in *.
    rewrite nodup_In. apply in_app_iff. auto.
  Qed.

  Lemma l_evs_prop :
    forall src1 src2 name
      (NOREPET1 : Coqlib.list_norepet (name1 (ext_funsL src1) ++ ext_varsL src1 ++
                                       name2 (prog_funsL src1) ++ name1 (prog_varsL src1)))
      (NOREPET2 : Coqlib.list_norepet (name1 (ext_funsL src2) ++ ext_varsL src2 ++
                                       name2 (prog_funsL src2) ++ name1 (prog_varsL src2)))
      (IN1 : In name (ext_varsL src1))
      (IN2 : In name (ext_varsL src2)),
      <<INLEVS: In (compile_eVar name) (compile_eVars (l_evs src1 src2))>>.
  Proof.
    ii. red. unfold l_evs, compile_eVars. apply in_map. apply filter_In. split.
    2:{ unfold name1, l_pvs. apply negb_true_iff. apply sumbool_to_bool_is_false. ii. ss.
        rewrite map_app in H. apply in_app_iff in H. des.
        - depgen src1; clear; i.
          rewrite Coqlib.list_norepet_app in NOREPET1. des. clear NOREPET1 NOREPET2.
          rewrite Coqlib.list_norepet_app in NOREPET0. des. clear NOREPET1 NOREPET0.
          unfold Coqlib.list_disjoint in NOREPET2. hexploit NOREPET2.
          { eapply IN1. }
          { rewrite in_app_iff; right. eauto. }
          ii; clarify.
        - depgen src2; clear; i.
          rewrite Coqlib.list_norepet_app in NOREPET2. des. clear NOREPET1 NOREPET2.
          rewrite Coqlib.list_norepet_app in NOREPET0. des. clear NOREPET1 NOREPET0.
          unfold Coqlib.list_disjoint in NOREPET2. hexploit NOREPET2.
          { eapply IN2. }
          { rewrite in_app_iff; right. eauto. }
          ii; clarify.
    }
    rewrite nodup_In. apply in_app_iff. auto.
  Qed.

End SOLVEID.



Section UNLINK.

  Lemma unlink_l_evs
        vd src1 src2
        (INL: In vd (l_evs src1 src2))
  :
    (<<IN1: In vd (ext_varsL src1)>>) \/ (<<IN2: In vd (ext_varsL src2)>>).
  Proof.
    unfold l_evs in INL. apply filter_In in INL. des. apply nodup_In in INL. apply in_app_iff in INL; auto.
  Qed.

  Lemma unlink_l_efs
        fd src1 src2
        (INL: In fd (l_efs src1 src2))
  :
    (<<IN1: In fd (ext_funsL src1)>>) \/ (<<IN2: In fd (ext_funsL src2)>>).
  Proof.
    unfold l_efs in INL. apply filter_In in INL. des. apply nodup_In in INL. apply in_app_iff in INL; auto.
  Qed.

  Lemma unlink_l_pvs
        vd src1 src2
        (INL: In vd (l_pvs src1 src2))
  :
    (<<IN1: In vd (prog_varsL src1)>>) \/ (<<IN2: In vd (prog_varsL src2)>>).
  Proof.
    unfold l_pvs in INL. apply in_app_iff in INL; auto.
  Qed.

  Lemma unlink_l_pfs
        fd src1 src2
        (INL: In fd (l_pfs src1 src2))
  :
    (<<IN1: In fd (prog_funsL src1)>>) \/ (<<IN2: In fd (prog_funsL src2)>>).
  Proof.
    unfold l_pfs in INL. apply in_app_iff in INL; auto.
  Qed.

End UNLINK.



Section LINKPROPS.

  Lemma link_imp_cond1_comm :
    forall src1 src2,
      <<LC1: link_imp_cond1 src1 src2 = true -> link_imp_cond1 src2 src1 = true>>.
  Proof.
    ii. apply link_imp_cond1_prop in H. des. unfold link_imp_cond1. bsimpl. repeat (try split).
    all: apply sumbool_to_bool_is_true.
    - depgen EV2; clear; i. unfold l_pfs in *. unfold name2 in *. rewrite map_app in *.
      eapply Cminorgenproof.permutation_norepet. 2:{ eauto. }
      apply Permutation_app_head. apply Permutation_app_comm.
    - depgen EV1; clear; i. unfold l_pfs in *. unfold name2 in *. rewrite map_app in *.
      eapply Cminorgenproof.permutation_norepet. 2:{ eauto. }
      apply Permutation_app_head. apply Permutation_app_comm.
    - depgen EF0; clear; i. unfold l_pvs in *. unfold name1 in *. rewrite map_app in *.
      eapply Cminorgenproof.permutation_norepet. 2:{ eauto. }
      apply Permutation_app_head. apply Permutation_app_comm.
    - depgen EF1; clear; i. unfold l_pvs in *. unfold name1 in *. rewrite map_app in *.
      eapply Cminorgenproof.permutation_norepet. 2:{ eauto. }
      apply Permutation_app_head. apply Permutation_app_comm.
    - depgen EVF2; clear; i. auto.
    - depgen EVF1; clear; i. auto.
  Qed.

  Lemma link_imp_cond2_comm :
    forall src1 src2,
      <<LC2: link_imp_cond2 src1 src2 = true -> link_imp_cond2 src2 src1 = true>>.
  Proof.
    ii. unfold link_imp_cond2 in *. eapply _link_imp_cond2_prop_perm.
    2:{ eapply H. }
    apply Permutation_app_comm.
  Qed.

  Lemma link_then_unique_ids
        src1 src2 srcl
        (LINK : link_imp src1 src2 = Some srcl)
    :
      <<UIDS : Coqlib.list_norepet (name1 (compile_gdefs srcl))>>.
  Proof.
    unfold link_imp in LINK. des_ifs. bsimpl. des.
    rewrite <- compile_gdefs_preserves_names. ss. apply link_imp_cond3_prop in Heq0.
    apply Coqlib.list_map_norepet; eauto.
    i. ii. apply s2p_inj in H2. ss.
  Qed.

  Lemma link_then_exists_gd
        src1 src2 srcl id gd1 gd2
        (NOREPET1 : Coqlib.list_norepet (List.map fst (compile_gdefs src1)))
        (NOREPET2 : Coqlib.list_norepet (List.map fst (compile_gdefs src2)))
        (LINKSRC : link_imp src1 src2 = Some srcl)
        (IN1 : In (id, gd1) (compile_gdefs src1))
        (IN2 : In (id, gd2) (compile_gdefs src2))
    :
      exists gdl, (<<LINK: link gd1 gd2 = Some gdl>>) /\ (<<INL: In (id, gdl) (compile_gdefs srcl)>>).
  Proof.
    Local Transparent Linker_def. Local Transparent Linker_fundef.
    Local Transparent Linker_vardef. Local Transparent Linker_varinit.
    hexploit link_then_unique_ids; eauto. i. des. rename H into NOREPETL.
    hexploit (decomp_gdefs IN1). i. rename H into SRC1.
    hexploit (decomp_gdefs IN2). i. rename H into SRC2.

    (* malloc *)
    destruct SRC1 as [SRC1 | SRC1].
    { clear SRC2. destruct SRC1. clarify. unfold compile_gdefs in IN2. apply in_app_or in IN2. des.
      - Local Transparent init_g. Local Transparent init_g0.
        unfold init_g in IN2. unfold init_g0 in IN2.
        Local Opaque init_g0. Local Opaque init_g.
        ss. des; clarify.
        + exists (Gfun (External EF_malloc)). split; ss; auto. apply has_malloc.
        + apply s2p_inj in H1. clarify.
      - apply malloc_unique in NOREPET2. eapply (in_map fst) in IN2. clarify. }
    destruct SRC2 as [SRC2 | SRC2].
    { clear SRC1. destruct SRC2. clarify. unfold compile_gdefs in IN1. apply in_app_or in IN1. des.
      - Local Transparent init_g. Local Transparent init_g0.
        unfold init_g in IN1. unfold init_g0 in IN1.
        Local Opaque init_g0. Local Opaque init_g.
        ss. des; clarify.
        + exists (Gfun (External EF_malloc)). split; ss; auto. apply has_malloc.
        + apply s2p_inj in H1. clarify.
      - apply malloc_unique in NOREPET1. eapply (in_map fst) in IN1. clarify. }

    (* free *)
    destruct SRC1 as [SRC1 | SRC1].
    { clear SRC2. destruct SRC1. clarify. unfold compile_gdefs in IN2. apply in_app_or in IN2. des.
      - Local Transparent init_g. Local Transparent init_g0.
        unfold init_g in IN2. unfold init_g0 in IN2.
        Local Opaque init_g0. Local Opaque init_g.
        ss. des; clarify.
        + apply s2p_inj in H1. clarify.
        + exists (Gfun (External EF_free)). split; ss; auto. apply has_free.
      - apply free_unique in NOREPET2. eapply (in_map fst) in IN2. clarify. }
    destruct SRC2 as [SRC2 | SRC2].
    { clear SRC1. destruct SRC2. clarify. unfold compile_gdefs in IN1. apply in_app_or in IN1. des.
      - Local Transparent init_g. Local Transparent init_g0.
        unfold init_g in IN1. unfold init_g0 in IN1.
        Local Opaque init_g0. Local Opaque init_g.
        ss. des; clarify.
        + apply s2p_inj in H1. clarify.
        + exists (Gfun (External EF_free)). split; ss; auto. apply has_free.
      - apply free_unique in NOREPET1. eapply (in_map fst) in IN1. clarify. }

    (* syscalls *)
    destruct SRC1 as [SRC1 | SRC1].
    { clear SRC2. des. clarify. unfold compile_gdefs in IN2.
      apply in_app_or in IN2. des.
      { apply (in_map (fst ∘ compile_eFun)) in SRC0. eapply syscalls_unique in NOREPET2.
        2:{ unfold c_sys. eapply SRC0. }
        clarify. exfalso. apply NOREPET2; clear NOREPET2. apply (in_map fst) in IN2. rewrite SRC1. ss. unfold name1.
        rewrite map_app. rewrite in_app_iff. left; auto. }
      apply in_app_or in IN2. des.
      2:{ apply (in_map (fst ∘ compile_eFun)) in SRC0. eapply syscalls_unique in NOREPET2.
          2:{ unfold c_sys. eapply SRC0. }
          clarify. exfalso. apply NOREPET2; clear NOREPET2. apply (in_map fst) in IN2. rewrite SRC1. ss. unfold name1.
          rewrite map_app. rewrite in_app_iff. right; auto. }
      apply decomp_c_sys in IN2. des. ss; clarify. unfold compile_eFun in *. destruct fd; destruct fd0. ss; clarify.
      apply s2p_inj in H1. clarify.
      eapply (in_compile_gdefs_c_sys srcl) in IN0.
      eapply (in_compile_gdefs_c_sys srcl) in SRC0.
      unfold compile_eFun in *. hexploit (compile_gdefs_unique_defs NOREPETL IN0 SRC0); eauto.
      i. eexists. split.
      2:{ eapply IN0. }
      rewrite H. red. clear. ss. des_ifs. }
    destruct SRC2 as [SRC2 | SRC2].
    { clear SRC1. des. clarify. unfold compile_gdefs in IN1.
      apply in_app_or in IN1. des.
      { apply (in_map (fst ∘ compile_eFun)) in SRC0. eapply syscalls_unique in NOREPET1.
        2:{ unfold c_sys. eapply SRC0. }
        clarify. exfalso. apply NOREPET1; clear NOREPET1. apply (in_map fst) in IN1. rewrite SRC2. ss. unfold name1.
        rewrite map_app. rewrite in_app_iff. left; auto. }
      apply in_app_or in IN1. des.
      2:{ apply (in_map (fst ∘ compile_eFun)) in SRC0. eapply syscalls_unique in NOREPET1.
          2:{ unfold c_sys. eapply SRC0. }
          clarify. exfalso. apply NOREPET1; clear NOREPET1. apply (in_map fst) in IN1. rewrite SRC2. ss. unfold name1.
          rewrite map_app. rewrite in_app_iff. right; auto. }
      apply decomp_c_sys in IN1. des. ss; clarify. unfold compile_eFun in *. destruct fd; destruct fd0. ss; clarify.
      apply s2p_inj in H1. clarify.
      eapply (in_compile_gdefs_c_sys srcl) in IN0.
      eapply (in_compile_gdefs_c_sys srcl) in SRC0.
      unfold compile_eFun in *. hexploit (compile_gdefs_unique_defs NOREPETL IN0 SRC0); eauto.
      i. eexists. split.
      2:{ eapply IN0. }
      rewrite H. red. clear. ss. des_ifs. }

    (* symbol resolution *)
    clear IN1 IN2. unfold link_imp in LINKSRC. des_ifs_safe. bsimpl. destruct Heq. destruct H.
    rename H into LC1, H1 into LC2, H0 into LC3.
    des.
    
    - (* ef/ef *)
      apply link_imp_cond2_prop in LC2.
      assert (snd fd0 = snd fd).
      { eapply LC2. repeat split.
        - rewrite in_app_iff. left; auto.
        - rewrite in_app_iff. right; auto.
        - unfold compile_eFun in *; ss; clarify. destruct fd0; destruct fd; ss; clarify. apply s2p_inj in H1; ss.
      }
      unfold compile_eFun in *; ss; clarify. destruct fd0; destruct fd; ss; clarify. apply s2p_inj in H1; ss; clarify.
      exists (snd (compile_eFun (s0, n0))). unfold compile_eFun. split.
      { des_ifs. }
      red. unfold compile_gdefs. ss. do 2 (apply in_app_iff; right). apply in_app_iff; left.
      apply unique_gdefs_unique_name in NOREPET1. apply unique_gdefs_unique_name in NOREPET2.
      eapply l_efs_prop; eauto.

    - (* ev/ef *)
      clear NOREPETL. exfalso. apply link_imp_cond1_prop in LC1. des.
      apply Coqlib.list_norepet_app in EVF1. des. unfold Coqlib.list_disjoint in EVF3.
      hexploit EVF3; eauto. unfold compile_eVar in *. ss; clarify. unfold compile_eFun in *. ss; clarify.
      destruct fd; ss; clarify. apply s2p_inj in H1. clarify. apply (in_map fst) in EFS0. ss.

    - (* if/ef *)
      exists (snd (compile_iFun fd0)). split.
      { destruct fd0 as [mn [fn impf]]. unfold compile_iFun in IFS. clarify; ss.
        destruct fd as [efn sig]. unfold compile_eFun in EFS. clarify; ss. }
      red. unfold compile_gdefs. ss. do 4 (rewrite in_app_iff; right). rewrite in_app_iff; left.
      unfold l_pfs. unfold compile_iFuns. rewrite map_app. rewrite in_app_iff; left.
      apply (in_map compile_iFun) in IFS0. rewrite IFS in *. ss.

    - (* iv/ef *)
      clear NOREPETL. exfalso. apply link_imp_cond1_prop in LC1. des.
      apply Coqlib.list_norepet_app in EF0. des. unfold Coqlib.list_disjoint in EF3.
      unfold name1 in EF3. apply (in_map fst) in EFS0. apply (in_map fst) in IVS0.
      hexploit EF3; eauto. unfold l_pvs. rewrite map_app. apply in_app_iff; left.
      destruct vd; destruct fd; ss. clarify. apply s2p_inj in H1; clarify; auto.

    - (* ef/ev *)
      clear NOREPETL. exfalso. apply link_imp_cond1_prop in LC1. des.
      apply Coqlib.list_norepet_app in EVF2. des. unfold Coqlib.list_disjoint in EVF3.
      hexploit EVF3; eauto. unfold compile_eVar in *. ss; clarify. unfold compile_eFun in *. ss; clarify.
      destruct fd; ss; clarify. apply s2p_inj in H1. clarify. apply (in_map fst) in EFS0. ss.

    - (* ev/ev *)
      exists (snd (compile_eVar vd0)). split.
      { unfold compile_eVar in *; ss; clarify. }
      red. unfold compile_gdefs; ss. do 3 (apply in_app_iff; right). apply in_app_iff; left.
      unfold compile_eVar in *; ss; clarify. apply s2p_inj in H1; clarify.
      apply unique_gdefs_unique_name in NOREPET1. apply unique_gdefs_unique_name in NOREPET2.
      eapply l_evs_prop; eauto.

    - (* if/ev *)
      clear NOREPETL. exfalso. apply link_imp_cond1_prop in LC1. des.
      apply Coqlib.list_norepet_app in EV2. des. unfold Coqlib.list_disjoint in EV3.
      unfold name2 in EV3. apply (in_map (fst ∘ snd)) in IFS0.
      hexploit EV3; eauto. unfold l_pfs. rewrite map_app. apply in_app_iff; left.
      destruct fd. destruct p. unfold compile_eVar in *; ss; clarify. apply s2p_inj in H1; clarify; auto.

    - (* iv/ev *)
      exists (snd (compile_iVar vd0)). split.
      { destruct vd0. unfold compile_eVar in *. ss; clarify. }
      red. unfold compile_gdefs; ss. do 5 (apply in_app_iff; right). unfold l_pvs.
      unfold compile_iVars. rewrite map_app. apply in_app_iff; left.
      apply (in_map compile_iVar) in IVS0. rewrite IVS in *. ss.

    - (* ef/if *)
      exists (snd (compile_iFun fd)). split.
      { destruct fd as [mn [fn impf]]. unfold compile_iFun in *. clarify; ss.
        destruct fd0 as [efn sig]. unfold compile_eFun in *. clarify; ss. }
      red. unfold compile_gdefs. ss. do 4 (rewrite in_app_iff; right). rewrite in_app_iff; left.
      unfold l_pfs. unfold compile_iFuns. rewrite map_app. rewrite in_app_iff; right.
      apply (in_map compile_iFun) in IFS0. rewrite IFS in *. ss.

    - (* ev/if *)
      clear NOREPETL. exfalso. apply link_imp_cond1_prop in LC1. des.
      apply Coqlib.list_norepet_app in EV1. des. unfold Coqlib.list_disjoint in EV3.
      unfold name2 in EV3. apply (in_map (fst ∘ snd)) in IFS0.
      hexploit EV3; eauto. unfold l_pfs. rewrite map_app. apply in_app_iff; right.
      destruct fd. destruct p. unfold compile_eVar in *; ss; clarify. apply s2p_inj in H1; clarify; auto.

    - (* if/if *)
      clear NOREPETL. exfalso. apply link_imp_cond3_ints in LC3. des. unfold Coqlib.list_disjoint in IFIF.
      unfold name2 in *. apply (in_map (fst ∘ snd)) in IFS2. apply (in_map (fst ∘ snd)) in IFS0.
      hexploit IFIF; eauto. ii. destruct fd0 as [mn0 [fn0 ff0]]; destruct fd as [mn [fn ff]]. ss; clarify.
      apply s2p_inj in H2; clarify.

    - (* iv/if *)
      clear NOREPETL. exfalso. apply link_imp_cond3_ints in LC3. des. unfold Coqlib.list_disjoint in IVIF.
      unfold name2 in *. unfold name1 in *. apply (in_map (fst ∘ snd)) in IFS0. apply (in_map fst) in IVS0.
      hexploit IVIF; eauto. ii. destruct vd; destruct fd as [mn [fn ff]]. ss; clarify.
      apply s2p_inj in H2; clarify.

    - (* ef/iv *)
      clear NOREPETL. exfalso. apply link_imp_cond1_prop in LC1. des.
      apply Coqlib.list_norepet_app in EF1. des. unfold Coqlib.list_disjoint in EF3.
      unfold name1 in EF3. apply (in_map fst) in EFS0. apply (in_map fst) in IVS0.
      hexploit EF3; eauto. unfold l_pvs. rewrite map_app. apply in_app_iff; right.
      destruct vd; destruct fd; ss. clarify. apply s2p_inj in H1; clarify; auto.

    - (* ev/iv *)
      exists (snd (compile_iVar vd)). split.
      { destruct vd. unfold compile_eVar in *. ss; clarify. }
      red. unfold compile_gdefs; ss. do 5 (apply in_app_iff; right). unfold l_pvs.
      unfold compile_iVars. rewrite map_app. apply in_app_iff; right.
      apply (in_map compile_iVar) in IVS0. rewrite IVS in *. ss.

    - (* if/iv *)
      clear NOREPETL. exfalso. apply link_imp_cond3_ints in LC3. des. unfold Coqlib.list_disjoint in IFIV.
      unfold name2 in *. unfold name1 in *. apply (in_map (fst ∘ snd)) in IFS0. apply (in_map fst) in IVS0.
      hexploit IFIV; eauto. ii. destruct vd; destruct fd as [mn [fn ff]]. ss; clarify.
      apply s2p_inj in H2; clarify.

    - (* iv/iv *)
      clear NOREPETL. exfalso. apply link_imp_cond3_ints in LC3. des. unfold Coqlib.list_disjoint in IVIV.
      unfold name1 in *. apply (in_map fst) in IVS2. apply (in_map fst) in IVS0.
      hexploit IVIV; eauto. ii. destruct vd0 as [vn0 vv0]; destruct vd as [vn vv]. ss; clarify.
      apply s2p_inj in H2; clarify.

      Local Opaque Linker_varinit. Local Opaque Linker_vardef.
      Local Opaque Linker_fundef. Local Opaque Linker_def.
  Qed.

  Lemma in_tgtl_then_in_some
        src1 src2 srcl id gd
        (LINKSRC : link_imp src1 src2 = Some srcl)
        (INL : In (id, gd) (compile_gdefs srcl))
    :
      (<<IN1: In (id, gd) (compile_gdefs src1)>>) \/ (<<BK: In (id, gd) (compile_gdefs src2)>>).
  Proof.
    unfold link_imp in LINKSRC. des_ifs; ss. apply decomp_gdefs in INL; des; ss; clarify.
    - left. red. eapply has_malloc.
    - left. red. eapply has_free.
    - left. red. rewrite <- SYS. apply in_compile_gdefs_c_sys. ss.
    - apply unlink_l_efs in EFS0. des.
      + left. rewrite <- EFS. apply in_compile_gdefs_efuns. ss.
      + right. rewrite <- EFS. apply in_compile_gdefs_efuns. ss.
    - apply unlink_l_evs in EVS0. des.
      + left. rewrite <- EVS. apply in_compile_gdefs_evars. ss.
      + right. rewrite <- EVS. apply in_compile_gdefs_evars. ss.
    - apply unlink_l_pfs in IFS0. des.
      + left. rewrite <- IFS. apply in_compile_gdefs_ifuns. ss.
      + right. rewrite <- IFS. apply in_compile_gdefs_ifuns. ss.
    - apply unlink_l_pvs in IVS0. des.
      + left. rewrite <- IVS. apply in_compile_gdefs_ivars. ss.
      + right. rewrite <- IVS. apply in_compile_gdefs_ivars. ss.
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

  Fixpoint nlist2list {A} (nl : Coqlib.nlist A) : list A :=
    match nl with
    | Coqlib.nbase a => [a]
    | Coqlib.ncons a nt => a :: (nlist2list nt)
    end.

  Fixpoint list2nlist {A} (a : A) (l : list A) : Coqlib.nlist A :=
    match l with
    | [] => Coqlib.nbase a
    | h :: t => Coqlib.ncons a (list2nlist h t)
    end.

  Lemma n2l_not_nil {A} :
    forall nl, @nlist2list A nl = [] -> False.
  Proof.
    i. induction nl; ss.
  Qed.

  Lemma n2l_cons_exists {A} :
    forall nl a b t (CONS: @nlist2list A nl = a :: b :: t),
      <<EXISTS: exists nt, (nlist2list nt = b :: t) /\ (nl = Coqlib.ncons a nt)>>.
  Proof.
    induction nl; i; ss; clarify.
    destruct t; ss; clarify.
    { exists nl. rewrite H0. ss. }
    eapply IHnl in H0. des. exists nl. split; eauto.
    rewrite H1. ss. rewrite H0. auto.
  Qed.

  Lemma n2l_l2n {A} :
    forall nl,
      (exists (h : A) t, (<<HT: nlist2list nl = h :: t>>) /\ (<<BACK: (list2nlist h t = nl)>>)).
  Proof.
    i. induction nl.
    - exists a, []. ss.
    - ss. des. exists a, (h :: t). ss. rewrite HT. split; ss. red. rewrite BACK. ss.
  Qed.

  Lemma l2n_n2l {A} :
    forall (h : A) t,
      (nlist2list (list2nlist h t)) = h :: t.
  Proof.
    i. depgen h. induction t; i; ss; clarify.
    f_equal. auto.
  Qed.

  Fixpoint link_imp_nlist (src_list : Coqlib.nlist Imp.programL) :=
    match src_list with
    | Coqlib.nbase a => Some a
    | Coqlib.ncons a l =>
      match link_imp_nlist l with
      | Some b => link_imp a b
      | None => None
      end
    end.

  Definition link_imp_list src_list :=
    match src_list with
    | [] => None
    | h :: t => link_imp_nlist (list2nlist h t)
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
    rename a into src1. des_ifs; ss; clarify. rename p into srct.
    hexploit IHsrc_list.
    2:{ eapply Heq. }
    { inv WFPROGS. ss. }
    i. red. eapply linked_two_wf with (src1:=src0) (src2:=srct); eauto.
    inv WFPROGS. auto.
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
