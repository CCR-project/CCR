Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
(* Require Import TODOYJ. *)
Require Import ProofMode.

Set Implicit Arguments.



Let _memRA: URA.t := (mblock ==> Z ==> (Excl.t val))%ra.
Compute (URA.car (t:=_memRA)).
Instance memRA: URA.t := Auth.t _memRA.
Compute (URA.car).

Local Arguments Z.of_nat: simpl nomatch.


Section PROOF.
  Context `{@GRA.inG memRA Σ}.

  Definition _points_to (loc: mblock * Z) (vs: list val): _memRA :=
    let (b, ofs) := loc in
    (fun _b _ofs => if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length vs))))%Z
                    then (List.nth_error vs (Z.to_nat (_ofs - ofs))) else ε)
  .

  (* Opaque _points_to. *)
  Lemma unfold_points_to loc vs:
    _points_to loc vs =
    let (b, ofs) := loc in
    (fun _b _ofs => if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length vs))))%Z
                    then (List.nth_error vs (Z.to_nat (_ofs - ofs))) else ε)
  .
  Proof. refl. Qed.

  Definition points_to (loc: mblock * Z) (vs: list val): memRA := Auth.white (_points_to loc vs).

  Definition var_points_to (skenv: SkEnv.t) (var: gname) (v: val): memRA :=
    match (skenv.(SkEnv.id2blk) var) with
    | Some  blk => points_to (blk, 0%Z) [v]
    | None => ε
    end.

  Lemma points_to_split
        blk ofs hd tl
    :
      (points_to (blk, ofs) (hd :: tl)) = (points_to (blk, ofs) [hd]) ⋅ (points_to (blk, (ofs + 1)%Z) tl)
  .
  Proof.
    ss. unfold points_to. unfold Auth.white. repeat (rewrite URA.unfold_add; ss).
    f_equal.
    repeat (apply func_ext; i).
    des_ifs; bsimpl; des; des_sumbool; subst; ss;
      try rewrite Z.leb_gt in *; try rewrite Z.leb_le in *; try rewrite Z.ltb_ge in *; try rewrite Z.ltb_lt in *; try lia.
    - clear_tac. subst. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      assert(x0 = ofs). { lia. } subst.
      rewrite Z.sub_diag in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq1; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq1; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      assert(x0 = ofs). { lia. } subst.
      rewrite Z.sub_diag in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
      rewrite Z.sub_add_distr in *. rewrite Z2Nat.inj_sub in Heq1; ss. rewrite T in *. ss. rewrite Nat.sub_0_r in *. ss.
    - clear_tac. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      assert(x0 = ofs). { lia. } subst.
      rewrite Z.sub_diag in *. ss.
  Qed.

(* Lemma points_tos_points_to *)
(*       loc v *)
(*   : *)
(*     (points_to loc v) = (points_tos loc [v]) *)
(* . *)
(* Proof. *)
(*   apply func_ext. i. *)
(*   apply prop_ext. *)
(*   ss. split; i; r. *)
(*   - des_ifs. ss. eapply Own_extends; et. rp; try refl. repeat f_equal. repeat (apply func_ext; i). *)
(*     des_ifs; bsimpl; des; des_sumbool; ss; clarify. *)
(*     + rewrite Z.sub_diag; ss. *)
(*     + rewrite Z.leb_refl in *; ss. *)
(*     + rewrite Z.ltb_ge in *. lia. *)
(*     + rewrite Z.ltb_lt in *. lia. *)
(*   - des_ifs. ss. eapply Own_extends; et. rp; try refl. repeat f_equal. repeat (apply func_ext; i). *)
(*     des_ifs; bsimpl; des; des_sumbool; ss; clarify. *)
(*     + rewrite Z.sub_diag; ss. *)
(*     + rewrite Z.ltb_lt in *. lia. *)
(*     + rewrite Z.leb_refl in *; ss. *)
(*     + rewrite Z.ltb_ge in *. lia. *)
(* Qed. *)

End PROOF.

Notation "loc |-> vs" := (points_to loc vs) (at level 20).



Section AUX.
  Context `{@GRA.inG memRA Σ}.

  Lemma points_to_disj
        ptr x0 x1
    :
      (OwnM (ptr |-> [x0]) -∗ OwnM (ptr |-> [x1]) -* ⌜False⌝)
  .
  Proof.
    destruct ptr as [blk ofs].
    iIntros "A B". iCombine "A B" as "A". iOwnWf "A" as WF0.
    unfold points_to in WF0. rewrite ! unfold_points_to in *. repeat (ur in WF0); ss.
    specialize (WF0 blk ofs). des_ifs; bsimpl; des; des_sumbool; zsimpl; ss; try lia.
  Qed.

  Fixpoint is_list (ll: val) (xs: list val): iProp :=
    match xs with
    | [] => (⌜ll = Vnullptr⌝: iProp)%I
    | xhd :: xtl =>
      (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl]))
                             ** is_list ltl xtl: iProp)%I
    end
  .

  Lemma unfold_is_list: forall ll xs,
      is_list ll xs =
      match xs with
      | [] => (⌜ll = Vnullptr⌝: iProp)%I
      | xhd :: xtl =>
        (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl]))
                               ** is_list ltl xtl: iProp)%I
      end
  .
  Proof.
    i. destruct xs; auto.
  Qed.

  Lemma unfold_is_list_cons: forall ll xhd xtl,
      is_list ll (xhd :: xtl) =
      (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl]))
                             ** is_list ltl xtl: iProp)%I.
  Proof.
    i. eapply unfold_is_list.
  Qed.

  Lemma is_list_wf
        ll xs
    :
      (is_list ll xs) -∗ (⌜(ll = Vnullptr) \/ (match ll with | Vptr _ 0 => True | _ => False end)⌝)
  .
  Proof.
    iIntros "H0". destruct xs; ss; et.
    { iPure "H0" as H0. iPureIntro. left. et. }
    iDestruct "H0" as (lhd ltl) "[[H0 H1] H2]".
    iPure "H0" as H0. iPureIntro. right. subst. et.
  Qed.

  (* Global Opaque is_list. *)
End AUX.





Section PROOF.
  Context `{@GRA.inG memRA Σ}.

  Definition alloc_spec: fspec :=
    (mk_simple (fun sz => (
                    (fun varg o => (⌜varg = [Vint (Z.of_nat sz)]↑ /\ (8 * (Z.of_nat sz) < modulus_64)%Z /\ o = ord_pure 0⌝: iProp)%I),
                    (fun vret => (∃ b, (⌜vret = (Vptr b 0)↑⌝)
                                         ** OwnM ((b, 0%Z) |-> (List.repeat Vundef sz))): iProp)%I
    ))).

  Definition free_spec: fspec :=
    (mk_simple (fun '(b, ofs) => (
                    (fun varg o => (∃ v, (⌜varg = ([Vptr b ofs])↑⌝)
                                           ** OwnM ((b, ofs) |-> [v]))
                                     ** ⌜o = ord_pure 0⌝),
                    fun vret => ⌜vret = (Vint 0)↑⌝%I
    ))).

  Definition load_spec: fspec :=
    (mk_simple (fun '(b, ofs, v) => (
                    (fun varg o => (⌜varg = ([Vptr b ofs])↑⌝)
                                     ** OwnM(((b, ofs) |-> [v]))
                                     ** (⌜o = ord_pure 0⌝)),
                    (fun vret => OwnM((b, ofs) |-> [v]) ** ⌜vret = v↑⌝)
    ))).

  Definition store_spec: fspec :=
    (mk_simple
       (fun '(b, ofs, v_new) => (
            (fun varg o => (∃ v_old,
                               (⌜varg = ([Vptr b ofs ; v_new])↑⌝)
                                 ** OwnM((b, ofs) |-> [v_old]))
                             ** (⌜o = ord_pure 0⌝)%I),
            (fun vret => OwnM((b, ofs) |-> [v_new]) ** ⌜vret = (Vint 0)↑⌝
    )))).

  Definition cmp_spec: fspec :=
    (mk_simple
       (fun '(result, resource) => (
            (fun varg o =>
               ((∃ b ofs v, ⌜varg = [Vptr b ofs; Vnullptr]↑⌝ ** ⌜resource = ((b, ofs) |-> [v])⌝ ** ⌜result = false⌝) ∨
                (∃ b ofs v, ⌜varg = [Vnullptr; Vptr b ofs]↑⌝ ** ⌜resource = ((b, ofs) |-> [v])⌝ ** ⌜result = false⌝) ∨
                (∃ b0 ofs0 v0 b1 ofs1 v1, ⌜varg = [Vptr b0 ofs0; Vptr b1 ofs1]↑⌝ ** ⌜resource = (((b0, ofs0) |-> [v0])) ⋅ ((b1, ofs1) |-> [v1])⌝ ** ⌜result = false⌝) ∨
                (∃ b ofs v, ⌜varg = [Vptr b ofs; Vptr b  ofs]↑⌝ ** ⌜resource = ((b, ofs) |-> [v])⌝ ** ⌜result = true⌝) ∨
                (⌜varg = [Vnullptr; Vnullptr]↑ /\ result = true⌝))
                 ** OwnM(resource)
                 ** ⌜o = ord_pure 0⌝
            ),
            (fun vret => OwnM(resource) ** ⌜vret = (if result then Vint 1 else Vint 0)↑⌝)
    ))).

  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("alloc", alloc_spec) ; ("free", free_spec) ; ("load", load_spec) ; ("store", store_spec) ; ("cmp", cmp_spec)].
  Defined.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("alloc", mk_specbody alloc_spec (fun _ => trigger (Choose _)));
    ("free",   mk_specbody free_spec (fun _ => trigger (Choose _)));
    ("load",   mk_specbody load_spec (fun _ => trigger (Choose _)));
    ("store",  mk_specbody store_spec (fun _ => trigger (Choose _)));
    ("cmp",    mk_specbody cmp_spec (fun _ => trigger (Choose _)))
    ]
  .

  Let initial_mr (sk: Sk.t): _memRA :=
    fun blk ofs =>
      match List.nth_error sk blk with
      | Some (_, gd) =>
        match gd with
        | Sk.Gfun => ε
        | Sk.Gvar gv => if (dec ofs 0%Z) then Some (Vint gv) else ε
        end
      | _ => ε
      end.

  Definition SMemSem (sk: Sk.t): SModSem.t := {|
    SModSem.fnsems := MemSbtb;
    SModSem.mn := "Mem";
    SModSem.initial_mr := (GRA.embed (Auth.black (initial_mr sk)));
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SMem: SMod.t := {|
    SMod.get_modsem := SMemSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition Mem: Mod.t := (SMod.to_tgt (fun _ => to_stb [])) SMem.

End PROOF.
Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
