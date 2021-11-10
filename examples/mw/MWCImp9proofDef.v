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
  Definition wf_arr (arr: val): Prop :=
    match arr with
    | Vint n => n = 0%Z
    | Vptr _ ofs => ofs = 0%Z
    | _ => False
    end
  .

  Definition wf (ske: SkEnv.t): _ -> W -> Prop :=
    @mk_wf _ (option (Any.t * Any.t))
           (fun w0 st_src st_tgt => (
                {{"NORMAL": ∃ arr map, ⌜w0 = None ∧ st_src = (arr, map)↑ ∧ wf_arr arr⌝ **
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
End SIMMODSEM.
