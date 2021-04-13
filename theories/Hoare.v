Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Export HoareDef.
Require Import Hoareproof0 Hoareproof1.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.





Section CANCEL.

  Context `{Σ: GRA.t}.

  Variable md_tgt: ModL.t.
  Let ms_tgt: ModSemL.t := (ModL.get_modsem md_tgt (Sk.load_skenv md_tgt.(ModL.sk))).

  Variable sbtb: list (gname * fspecbody).
  Let stb: list (gname * fspec) := List.map (fun '(gn, fsb) => (gn, fsb_fspec fsb)) sbtb.

  Let md_mid: ModL.t := md_mid md_tgt sbtb.
  Let ms_mid: ModSemL.t := ms_mid md_tgt sbtb.

  Let md_src: ModL.t := md_src md_tgt sbtb.
  Let ms_src: ModSemL.t := ms_src md_tgt sbtb.

  Let rsum: r_state -> Σ :=
    fun '(mrs_tgt, frs_tgt) => (URA.add (fold_left URA.add (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε)
                                        (fold_left URA.add frs_tgt ε)).

  Hypothesis WTY: ms_tgt.(ModSemL.fnsems) = List.map (fun '(fn, sb) => (fn, (transl_all sb.(fsb_fspec).(mn)) <*> fun_to_tgt stb fn sb)) sbtb.
  Hypothesis WF1: Forall (fun '(_, sp) => In sp.(mn) (List.map fst ms_tgt.(ModSemL.initial_mrs))) stb.
  Variable entry_r: Σ.
  Variable main_pre: Any.t -> ord -> Σ -> Prop.
  Hypothesis MAIN: List.find (fun '(_fn, _) => dec "main" _fn) stb =
                   Some ("main", (mk_simple "Main" (fun (_: unit) => (main_pre, top2)))).
  Hypothesis MAINPRE: main_pre ([]: list val)↑ ord_top entry_r.
  Hypothesis WFR: URA.wf (entry_r ⋅ rsum (ModSemL.initial_r_state ms_tgt)).

  Theorem adequacy_type: Beh.of_program (ModL.compile md_tgt) <1= Beh.of_program (ModL.compile md_src).
  Proof.
    ii. eapply adequacy_type_m2s. eapply adequacy_type_t2m; et.
  Qed.

End CANCEL.
