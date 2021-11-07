Require Import HoareDef MWHeader MWCImp MWC9 SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import HTactics.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.
Require Import HTactics ProofMode IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen STB.

Set Implicit Arguments.

Local Open Scope nat_scope.


Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Definition le (w0 w1: option (Any.t * Any.t)): Prop :=
    match w0, w1 with
    | Some w0, Some w1 => w0 = w1
    | None, None => True
    | _, _ => False
    end
  .

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. unfold le. ii. des_ifs. Qed.
  Next Obligation. unfold le. ii. des_ifs. Qed.

  Let W: Type := Any.t * Any.t.

  (* Let wf: unit -> W -> Prop := *)
  (*   fun _ '(mrps_src0, mrps_tgt0) => *)
  (*     (<<SRC: mrps_src0 = tt↑>>) /\ *)
  (*     (<<TGT: mrps_tgt0 = tt↑>>) *)
  (* . *)
  Let wf (ske: SkEnv.t): _ -> W -> Prop :=
    @mk_wf _ (option (Any.t * Any.t))
           (fun w0 st_src st_tgt => (
                {{"NORMAL": ∃ arr map, ⌜w0 = None ∧ st_src = (arr, map)↑⌝ **
                    OwnM (var_points_to ske "gv0" arr) ** OwnM (var_points_to ske "gv1" map)}} ∨
                (* {{"NORMAL": ∃ arr map arrb mapb, ⌜w0 = None ∧ ske.(SkEnv.id2blk) "gv0" = Some arrb *)
                (*     ∧ ske.(SkEnv.id2blk) "gv1" = Some mapb ∧ st_src = (arr, map)↑⌝ ** *)
                (*     OwnM ((arrb, 0%Z) |-> [arr]) ** OwnM ((mapb, 0%Z) |-> [map ])}} ∨ *)
                {{"LOCKED": ⌜(∃ p0, st_src = Any.pair tt↑ p0) ∧ w0 = Some (st_src, st_tgt)⌝%I}})%I
              (* ⌜True⌝ ** (∃ (stk_mgr0: gmap mblock (list val)), *)
              (*            (⌜_stk_mgr0 = stk_mgr0↑⌝) ∧ *)
              (*            ({{"SIM": ([∗ map] handle ↦ stk ∈ stk_mgr0, *)
              (*                       (∃ hd, OwnM ((handle, 0%Z) |-> [hd]) ** is_list hd stk))}}) *)
           )
  .

  Variable global_stb: gname -> option fspec.
  Hypothesis STBINCL: stb_incl (to_stb (MWStb ++ MemStb)) global_stb.

  Import ImpNotations.

  Theorem correct:
    refines2 [MWCImp.MW] [MWC9.MW (fun _ => global_stb)].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    econstructor 1 with (wf:=wf (Sk.load_skenv sk)) (le:=top2); et; ss; cycle 1.
    { exists None. econs. eapply to_semantic. iIntros "[A B]". iLeft. iSplits; ss; et. iFrame.
      iSplits; ss; et. }
    econs; ss.
    { kinit. harg. mDesAll; des; clarify. unfold mainF, MWCImp.mainF.
      Ltac isteps := repeat (steps; imp_steps).
      isteps. rewrite unfold_eval_imp. isteps.
      des_ifs.
      contradict n.
      solve_NoDup.
      list_tac.
      try lia.
      des_ifs_safe ltac:(try lia). ss.
      steps. 
    }
    unfold fF.
    unfold IntroFImpA.fF.
    (* Local Opaque vadd. *)
    steps.
    rewrite unfold_eval_imp. cbn. steps.
    (* eapply Any.downcast_upcast in _UNWRAPN. des. *)
    unfold unint, ccallU in *. destruct v; clarify; ss.
    des_ifs; try (by exfalso; apply n; solve_NoDup).
    - repeat (steps; (des_ifs; try lia; []); imp_steps). r; esplits; et.
    - repeat (steps; (des_ifs; try lia; []); imp_steps). r; esplits; et.
    - repeat (steps; (des_ifs; try lia; []); imp_steps).
      unfold Ncall.
      steps. des_ifs.
      + repeat (steps; (des_ifs; try lia; []); imp_steps).
        force_l. exists false. steps. force_l. esplits. steps.
        force_l; ss. repeat (steps; (des_ifs; try lia; []); imp_steps).
        rewrite Z.eqb_eq in *. clarify.
        r; esplits; et.
      + repeat (steps; (des_ifs; try lia; []); imp_steps).
        force_l. exists true.
        unfold ccallU.
        repeat (steps; (des_ifs; try lia; []); imp_steps).
        force_l; ss.
        repeat (steps; (des_ifs; try lia; []); imp_steps).
        r; esplits; et. do 2 f_equal. lia.
  Unshelve. all: try exact 0. all: ss.
  Qed.

End SIMMODSEM.
