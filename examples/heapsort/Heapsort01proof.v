Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import HeapsortHeader.
Require Import HeapsortProperties.
Require Import Heapsort0 Heapsort1.
Require Import HTactics ProofMode.
Require Import SimModSem.
Require Import Coq.Sorting.Sorted.

Section SIMMODSEM.

  (* Context `{Σ : GRA.t}. *)

  (* Variable GlobalStb : Sk.t -> gname -> option fspec. *)
  (* Hypothesis STBINCL : forall sk, stb_incl (to_stb SHeapsortStb) (GlobalStb sk). *)
  (* Hint Unfold SHeapsortStb : stb. *)

  (* Definition wf : _ -> Any.t * Any.t -> Prop := *)
  (*   @mk_wf *)
  (*     _ *)
  (*     unit *)
  (*     (fun _ st_src st_tgt => True)%I. *)

  

  (* Theorem correct : refines2 [Heapsort0.Heapsort] [Heapsort1.Heapsort_to0 GlobalStb]. *)
  (* Proof. *)
  (* Admitted. *)
End SIMMODSEM.
