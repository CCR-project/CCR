Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Ordinal ClassicalOrdinal.
Require Import Any.
Require Export HoareDef.
Require Import Hoareproof0 Hoareproof1.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.





Section CANCEL.

  Context `{Σ: GRA.t}.
  Opaque GRA.to_URA.

  Variable md_tgt: Mod.t.
  Let ms_tgt: ModSem.t := (Mod.get_modsem md_tgt (Sk.load_skenv md_tgt.(Mod.sk))).

  Variable sbtb: list (gname * fspecbody).
  Let stb: list (gname * fspec) := List.map (fun '(gn, fsb) => (gn, fsb_fspec fsb)) sbtb.

  Let md_mid: Mod.t := md_mid md_tgt sbtb.
  Let ms_mid: ModSem.t := ms_mid md_tgt sbtb.

  Let md_src: Mod.t := md_src md_tgt sbtb.
  Let ms_src: ModSem.t := ms_src md_tgt sbtb.

  Let rsum: r_state -> Σ :=
    fun '(mrs_tgt, frs_tgt) => (URA.add (fold_left URA.add (List.map (mrs_tgt <*> fst) ms_tgt.(ModSem.initial_mrs)) ε)
                                        (fold_left URA.add frs_tgt ε)).

  Hypothesis WTY: ms_tgt.(ModSem.fnsems) = List.map (fun '(fn, sb) => (fn, fun_to_tgt stb fn sb)) sbtb.
  Hypothesis WF1: Forall (fun '(_, sp) => In sp.(mn) (List.map fst ms_tgt.(ModSem.initial_mrs))) stb.
  Hypothesis MAIN: List.find (fun '(_fn, _) => dec "main" _fn) stb = Some ("main", (@mk_simple _ "Main" unit (fun _ _ _ o => o = ord_top) top3)).
  Hypothesis WFR: URA.wf (rsum (ModSem.initial_r_state ms_tgt)).

  Theorem adequacy_type: Beh.of_program (Mod.interp md_tgt) <1= Beh.of_program (Mod.interp md_src).
  Proof.
    ii. eapply adequacy_type_m2s. eapply adequacy_type_t2m; et.
  Qed.

End CANCEL.
