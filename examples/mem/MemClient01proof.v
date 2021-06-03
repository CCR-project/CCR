Require Import MemClient0 MemClient1 HoareDef SimModSem.
Require Import Coqlib.
Require Import Universe.
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
Require Import TODOYJ.
Require Import HTactics Logic IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen.

Set Implicit Arguments.

Local Open Scope nat_scope.





Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  (* Let wf: W -> Prop := top1. *)
  Let wf: W -> Prop := @mk_wf _ unit (fun _ _ _ => ⌜True⌝%I) (fun _ _ _ => ⌜True⌝%I).

  (* Definition __hide_mark A (a : A) : A := a. *)
  (* Lemma intro_hide_mark: forall A (a: A), a = __hide_mark a. refl. Qed. *)

  (* Ltac hide_k :=  *)
  (*   match goal with *)
  (*   | [ |- (gpaco6 _ _ _ _ _ _ _ _ (_, ?isrc >>= ?ksrc) (_, ?itgt >>= ?ktgt)) ] => *)
  (*     erewrite intro_hide_mark with (a:=ksrc); *)
  (*     erewrite intro_hide_mark with (a:=ktgt); *)
  (*     let name0 := fresh "__KSRC__" in set (__hide_mark ksrc) as name0; move name0 at top; *)
  (*     let name0 := fresh "__KTGT__" in set (__hide_mark ktgt) as name0; move name0 at top *)
  (*   end. *)

  (* Ltac unhide_k := *)
  (*   do 2 match goal with *)
  (*   | [ H := __hide_mark _ |- _ ] => subst H *)
  (*   end; *)
  (*   rewrite <- ! intro_hide_mark *)
  (* . *)

  Theorem sim_modsem: ModSemPair.sim (MemClient1.ClientSem (UnknownStb ++ ClientStb ++ MemStb)) MemClient0.ClientSem.
  Proof.
    econstructor 1 with (wf:=wf); ss; et; swap 2 3.
    { econs; ss.
      - eapply to_semantic; cycle 1. { eapply URA.wf_unit. } iIntros "H". iPureIntro. ss.
      - eapply to_semantic; cycle 1. { eapply URA.wf_unit. } iIntros "H". iPureIntro. ss.
    }
    econs; ss.
    { unfold clientF. init. harg. destruct varg_src.
      { ss. des_ifs; mDesAll; ss. }
      destruct x; mDesAll; ss. des; subst.
      unfold clientBody. steps. unfold KPC. steps.

      force_l. exists "alloc". steps. force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
      hcall _ (Some _) _ with ""; ss; et.
      { iModIntro. iSplitR; ss. iPureIntro. esplits; et. instantiate (1:=1%nat). ss. }
      { ss. }
      steps. mDesAll. subst. rewrite Any.upcast_downcast in *. clarify.

      force_l. exists "store". steps. force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
      hcall _ (Some (_, _, _)) _ with "A"; ss; et.
      { iModIntro. iSplitR; ss. iSplitL; ss.
        - iExists _. iSplitL; ss. iSplitR; ss.
        - ss.
      }
      { ss. }
      steps.

      force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
      hcall _ _ _ with ""; ss; et.
      { iModIntro. iSplitR; ss. iPureIntro. esplits; et. rewrite Any.upcast_downcast. ss. }
      { ss. }
      steps. mDesAll. subst.

      force_l. exists "load". steps. force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
      hcall _ (Some (_, _, _)) _ with "POST"; ss; et.
      { iModIntro. iSplitR; ss. iSplitL; ss.
        - iSplitL; ss. iSplitR; ss.
        - ss.
      }
      { ss. }
      steps. mDesAll. subst. rewrite Any.upcast_downcast in *. clarify.

      hret _; ss.
    }
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Theorem correct: ModPair.sim (MemClient1.Client (fun _ => (UnknownStb ++ ClientStb ++ MemStb)))
                               MemClient0.Client.
  Proof.
    econs; ss.
    { ii. eapply adequacy_lift. eapply sim_modsem. }
    ii; ss. repeat (econs; ss).
  Qed.

End SIMMOD.
