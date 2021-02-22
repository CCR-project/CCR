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

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.







Let _memRA: URA.t := (block ==> Z ==> (RA.excl val))%ra.
Compute (URA.car (t:=_memRA)).
Instance memRA: URA.t := URA.auth _memRA.
Compute (URA.car).


Section PROOF.
  Context `{@GRA.inG memRA Σ}.
  
  Definition points_to (loc: block * Z) (vs: list val): Σ :=
    let (b, ofs) := loc in
    let memr: memRA := URA.white (M:=_memRA)
                                 (fun _b _ofs => if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length vs))))%Z
                                                 then inl (List.nth_error vs (Z.to_nat (_ofs - ofs))) else inr tt) in
    (GRA.padding memr)
  .

  Lemma points_to_split
        blk ofs hd tl
    :
      (points_to (blk, ofs) (hd :: tl)) = (points_to (blk, ofs) [hd]) ⋅ (points_to (blk, (ofs + 1)%Z) tl)
  .
  Proof.
    ss. rewrite GRA.padding_add. repeat f_equal.
    ss. unfold URA.white. f_equal.
    repeat (apply func_ext; i).
    des_ifs; bsimpl; des; des_sumbool; ss; try rewrite Z.leb_gt in *; try rewrite Z.leb_le in *;
      try rewrite Z.ltb_ge in *; try rewrite Z.ltb_lt in *; try lia.
    - clear_tac. subst. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      assert(x0 = ofs).
      { lia. }
      subst.
      f_equal. rewrite Z.sub_diag. ss.
    - clear_tac. subst. rewrite Zpos_P_of_succ_nat in *. rewrite <- Zlength_correct in *.
      f_equal. clear Heq4. clear Heq5. clear_tac.
      destruct (Z.to_nat (x0 - ofs)) eqn:T; ss.
      { exfalso. lia. }
      f_equal. lia.
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





Section PROOF.
  Context `{@GRA.inG memRA Σ}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.

  Let alloc_spec: fspec := (mk_simple "Mem"
                                      (fun sz varg o _ => varg = [Vint (Z.of_nat sz)]↑ /\ o = ord_pure 1)
                                      (fun sz vret rret =>
                                         exists b, vret = (Vptr b 0)↑ /\
                                                   rret = (points_to (b, 0%Z) (List.repeat (Vint 0) sz)))).

  Let free_spec: fspec := (mk_simple "Mem"
                                     (fun '(b, ofs) varg o rarg => exists v, varg = ([Vptr b ofs])↑ /\
                                                                             rarg = ((b, ofs) |-> [v]) /\
                                                                             o = ord_pure 1)
                                     (top3)).

  Let load_spec: fspec := (mk_simple "Mem"
                                     (fun '(b, ofs, v) varg o rarg => varg = ([Vptr b ofs])↑ /\
                                                                      rarg = ((b, ofs) |-> [v]) /\
                                                                      o = ord_pure 1)
                                     (fun '(b, ofs, v) vret rret => rret = ((b, ofs) |-> [v]) /\ vret = v↑)).

  Let store_spec: fspec := (mk_simple
                              "Mem"
                              (fun '(b, ofs, v_new) varg o rarg => exists v_old,
                                   varg = ([Vptr b ofs ; v_new])↑ /\ rarg = ((b, ofs) |-> [v_old]) /\ o = ord_pure 1)
                              (fun '(b, ofs, v_new) _ rret => rret = ((b, ofs) |-> [v_new]))).

  Let cmp_spec: fspec :=
    (mk_simple
       "Mem"
       (fun '(result, resource) varg o rarg =>
          rarg = resource /\
          ((exists b ofs v, varg = [Vptr b ofs; Vnullptr]↑ /\ rarg = ((b, ofs) |-> v) /\ result = false) \/
           (exists b0 ofs0 v0 b1 ofs1 v1, varg = [Vptr b0 ofs0; Vptr b1 ofs1]↑ /\ rarg = ((b0, ofs0) |-> v0) ⋅ ((b1, ofs1) |-> v1) /\ result = false) \/
           (exists b ofs v, varg = [Vptr b ofs; Vptr b ofs]↑ /\ rarg = ((b, ofs) |-> v) /\ result = true)
          )
       )
       (fun '(result, resource) varg rret => varg = result↑ /\ rret = resource)
    ).

  Definition MemStb: list (gname * fspec) :=
    [("alloc", alloc_spec) ; ("free", free_spec) ; ("load", load_spec) ; ("store", store_spec) ; ("cmp", cmp_spec)]
  .

  Definition MemSbtb: list (gname * fspecbody) :=
    [("alloc", mk_specbody alloc_spec (fun _ => trigger (Choose _)));
    ("free",   mk_specbody free_spec (fun _ => trigger (Choose _)));
    ("load",   mk_specbody load_spec (fun _ => trigger (Choose _)));
    ("store",  mk_specbody store_spec (fun _ => trigger (Choose _)));
    ("cmp",    mk_specbody cmp_spec (fun _ => trigger (Choose _)))
    ]
  .

  Definition MemSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fsb) => (fn, fun_to_tgt MemStb fn fsb)) MemSbtb;
    ModSem.initial_mrs :=
      [("Mem", (GRA.padding (URA.black (M:=_memRA)
                            (fun b ofs => if (b =? 0)%nat && (ofs =? 0)%Z then inl (Some Vundef) else inr tt)), tt↑))];
  |}
  .

  Definition Mem: Mod.t := {|
    Mod.get_modsem := fun _ => MemSem; (*** TODO: we need proper handling of function pointers ***)
    Mod.sk := List.map (fun '(n, _) => (n, Sk.Gfun)) MemStb;
  |}
  .

End PROOF.
