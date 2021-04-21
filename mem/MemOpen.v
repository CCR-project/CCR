Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic.
Require Import TODO.
Require Import Mem0.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Let _memRA: URA.t := (block ==> Z ==> (Excl.t val))%ra.
Compute (URA.car (t:=_memRA)).
Instance memRA: URA.t := Auth.t _memRA.
Compute (URA.car).

Section PROOF.
  Context `{@GRA.inG memRA Σ}.

  Definition _points_to (loc: block * Z) (vs: list val): _memRA :=
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

  Definition points_to (loc: block * Z) (vs: list val): memRA := Auth.white (_points_to loc vs).

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





Definition dead_extend (m0: Mem.t) (delta: nat): Mem.t :=
  Mem.mk m0.(Mem.cnts) (m0.(Mem.nb) + delta)
.

Section PROOF.
  Context `{@GRA.inG memRA Σ}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.

  Definition expose X (PQ: X -> ((Any.t -> ord -> iProp) * (Any.t -> iProp))): fspec :=
    @mk _ (X * bool)%type (list val * bool)%type val
        (fun '(x, is_p) argh argl o => ⌜argh↑ = Any.pair argl is_p↑⌝ ** (⌜is_p⌝ -* ((fst ∘ PQ) x argl o)))
        (fun '(x, is_p) reth retl   => ⌜reth↑ = retl⌝ ** (⌜is_p⌝ -* ((snd ∘ PQ) x retl)))
  .




  Definition alloc_spec: fspec :=
    (expose (fun sz => (
                 (fun varg o => ⌜varg = [Vint (Z.of_nat sz)]↑ /\ o = ord_pure 1⌝),
                 (fun vret => Exists b, ⌜vret = (Vptr b 0)↑⌝ **
                                                          Own(GRA.embed ((b, 0%Z) |-> (List.repeat (Vint 0) sz))))
    ))).
  Definition alloc_body: (list val * bool) -> itree (hCallE +' pE +' eventE) val :=
    fun '(varg, is_p) =>
      if is_p
      then (
          (*** No non-deterministic allocation; it should be APC ***)
          trigger (Choose _)
        )
      else (
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        `sz: Z <- (pargs [Tint] varg)?;;
        delta <- trigger (Choose _);;
        let m0': Mem.t := dead_extend m0 delta in
        let (blk, m1) := Mem.alloc m0' sz in
        trigger (PPut m1↑);;
        Ret (Vptr blk 0)
        )
  .
  Definition alloc_fsb: fspecbody := mk_specbody alloc_spec alloc_body.




  Definition free_spec: fspec :=
    (expose (fun '(b, ofs) => (
                 (fun varg o => Exists v, ⌜varg = ([Vptr b ofs])↑⌝ **
                                                                Own(GRA.embed ((b, ofs) |-> [v])) **
                                                                ⌜o = ord_pure 1⌝),
                 top2
    ))).
  Definition free_body: (list val * bool) -> itree (hCallE +' pE +' eventE) val :=
    fun '(varg, is_p) =>
      if is_p
      then trigger (Choose _)
      else (
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(b, ofs) <- (pargs [Tptr] varg)?;;
        m1 <- (Mem.free m0 b ofs)?;;
        trigger (PPut m1↑);;
        Ret (Vint 0)
        )
  .
  Definition free_fsb: fspecbody := mk_specbody free_spec free_body.




  Definition load_spec: fspec :=
    (expose (fun '(b, ofs, v) => (
                 (fun varg o => ⌜varg = ([Vptr b ofs])↑⌝ **
                                                      Own(GRA.embed ((b, ofs) |-> [v])) **
                                                      ⌜o = ord_pure 1⌝),
                 (fun vret => Own(GRA.embed ((b, ofs) |-> [v])) ** ⌜vret = v↑⌝)
    ))).
  Definition load_body: (list val * bool) -> itree (hCallE +' pE +' eventE) val :=
    fun '(varg, is_p) =>
      if is_p
      then trigger (Choose _)
      else (
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(b, ofs) <- (pargs [Tptr] varg)?;;
        v <- (Mem.load m0 b ofs)?;;
        Ret v
        )
  .
  Definition load_fsb: fspecbody := mk_specbody load_spec load_body.




  Definition store_spec: fspec :=
    (expose
       (fun '(b, ofs, v_new) => (
            (fun varg o => Exists v_old,
                           ⌜varg = ([Vptr b ofs ; v_new])↑⌝ ** Own(GRA.embed ((b, ofs) |-> [v_old])) ** ⌜o = ord_pure 1⌝),
            (fun _ => Own(GRA.embed ((b, ofs) |-> [v_new])))
    )))
  .
  Definition store_body: (list val * bool) -> itree (hCallE +' pE +' eventE) val :=
    fun '(varg, is_p) =>
      if is_p
      then trigger (Choose _)
      else (
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(b, ofs, v) <- (pargs [Tptr; Tuntyped] varg)?;;
        m1 <- (Mem.store m0 b ofs v)?;;
        trigger (PPut m1↑);;
        Ret (Vint 0)
        )
  .
  Definition store_fsb: fspecbody := mk_specbody store_spec store_body.




  Definition cmp_spec: fspec := mk_simple (X:=unit) (fun _ => ((fun _ _ => ⌜True⌝), (fun _ => ⌜True⌝))).
  Definition cmp_fsb: fspecbody := mk_specbody cmp_spec (fun _ => triggerUB).




  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("alloc", alloc_spec) ; ("free", free_spec) ; ("load", load_spec) ; ("store", store_spec) ; ("cmp", cmp_spec)].
  Defined.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("alloc", alloc_fsb);
    ("free",   free_fsb);
    ("load",   load_fsb);
    ("store",  store_fsb);
    ("cmp",    cmp_fsb)
    ]
  .

  Definition SMemSem: SModSem.t := {|
    SModSem.fnsems := MemSbtb;
    SModSem.mn := "Mem";
    SModSem.initial_mr := (GRA.embed (Auth.black (M:=_memRA) ε));
    SModSem.initial_st := tt↑;
  |}
  .

  Definition MemSem: ModSem.t := (SModSem.to_tgt MemStb) SMemSem.

  Definition SMem: SMod.t := {|
    SMod.get_modsem := fun _ => SMemSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition Mem: Mod.t := (SMod.to_tgt MemStb) SMem.

End PROOF.
Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
