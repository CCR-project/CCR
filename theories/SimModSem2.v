Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIM.

  Context `{GRA: GRA.t}.

  Let st_local: Type := ((string -> GRA) * GRA).

  Variable SR: relation st_local.

  Set Typeclasses Depth 5.
  Definition handle_rE_local `{eventE -< E}: rE ~> stateT st_local (itree E) :=
    fun _ e '(mrs, fr0) =>
    match e with
    | Put mn mr fr1 =>
      guarantee(URA.updatable (URA.add (mrs mn) fr0) (URA.add mr fr1));;
      Ret (((update mrs mn mr), fr1), tt)
    | MGet mn => Ret ((mrs, fr0), mrs mn)
    | FGet => Ret ((mrs, fr0), fr0)
    | Forge rarg => Ret ((mrs, URA.add fr0 rarg), tt)
    | Discard rret =>
      fr1 <- trigger (Choose _);;
      guarantee(fr0 = URA.add fr1 rret);;
      Ret ((mrs, fr1), tt)
    | CheckWf mn =>
      assume(URA.wf (URA.add (mrs mn) fr0));;
      Ret ((mrs, fr0), tt)
    (* | PushFrame => triggerUB *)
    (* | PopFrame => triggerUB *)
    | _ => triggerUB
    end
  .

  (*** anyhow, rE is erased ... ***)
  Definition interp_rE_local D `{eventE -< E}:
    itree (D +' rE +' E) ~> stateT st_local (itree (D +' E)).
    eapply State.interp_state.
    i. destruct X.
    { eapply State.pure_state. apply (inl1 d). }
    destruct s.
    { eapply handle_rE_local. apply r. }
    { eapply State.pure_state. apply (inr1 e). }
  Defined.

  (* Q: nat -> forall T or forall T, nat -> ???? *)
  Section PLAYGROUND.
    Variable A B: Type.
    Variable k: B -> Type.
    Let obj0: Type := A -> forall (b: B), k b.
    Let obj1: Type := forall (b: B), A -> k b.
    Let bij: obj0 -> obj1.
      ii. eapply X; eauto.
    Defined.
    Require Import FinFun.
    Theorem bijective: Bijective bij.
    Proof.
      rr. unshelve eexists.
      { ii. eapply X; et. }
      esplits; eauto.
    Qed.
  End PLAYGROUND.



  Section SIMITREE.
    Variable T: Type.
    Inductive _sim_itree sim_itree: nat -> relation (itree (callE +' eventE) T) :=
    | sim_itree_ret
        i0 t
      :
        _sim_itree sim_itree i0 (Ret t) (Ret t)
    | sim_itree_call
        i0
        fn varg k_src k_tgt
        (K: forall vret, exists (i1: nat), sim_itree i1 (k_src vret) (k_src vret))
      :
        _sim_itree sim_itree i0 (Vis (subevent _ (Call fn varg)) k_src)
                  (Vis (subevent _ (Call fn varg)) k_tgt)
    (* | sim_itree_choose_src *)
    (* | sim_itree_choose_tgt *)
    (* | sim_itree_take_src *)
    (* | sim_itree_take_tgt *)
    (* | sim_itree_syscall_src *)
    (* | sim_itree_syscall_tgt *)
    (* | sim_itree_tau_src *)
    (* | sim_itree_tau_tgt *)
    .

    (*** prove nice properties, (transitivity, etc) ***)

    Definition sim_itree: _ -> relation _ := paco3 _sim_itree bot3.
  End SIMITREE.



  (* Eval red in (stateT st_local (itree (callE +' eventE)) val). *)
  (* Let sim_ktree: nat -> relation (stateT st_local (itree (callE +' eventE)) val). *)
  (* Proof. *)
  (*   intro n. r. intros k_src k_tgt. *)
  (*   r in k_src. r in k_tgt. *)
  (*   eapply respectful; cycle 2. *)
  (*   { apply k_src. } *)
  (*   { apply k_tgt. } *)
  (*   { apply SR. } *)
  (*   apply sim_itree. apply n. *)
  (* Defined. *)

  (* Let sim_fn: relation (list val -> itree Es val). *)
  (*   eapply respectful. *)
  (*   - r. eapply eq. *)
  (*   - r. intros it_src it_tgt. *)
  (*     apply interp_rE_local in it_src; cycle 1. *)
  (*     { ss. } *)
  (*     apply interp_rE_local in it_tgt; cycle 1. *)
  (*     { ss. } *)
  (*     apply (exists n, sim_ktree n it_src it_tgt). *)
  (* Defined. *)

  Definition sim_ktree: nat -> relation (stateT st_local (itree (callE +' eventE)) val) :=
    fun n k_src k_tgt => (SR ==> sim_itree n)%signature k_src k_tgt.

  Definition sim_fsem: relation (list val -> itree Es val) :=
    (eq ==> (fun it_src it_tgt => exists n, sim_ktree n (interp_rE_local it_src)
                                                      (interp_rE_local it_tgt)))%signature.

  Definition sim_fnsem: relation (string * (list val -> itree Es val)) := RelProd eq sim_fsem.

End SIM.



Section SIMMODSEM.

  Context `{GRA: GRA.t}.
  Variable (ms0 ms1: ModSem.t).

  Inductive sim: Prop := mk {
    SR: relation ((string -> GRA) * GRA);
    sim_fnsems: Forall2 (sim_fnsem SR) ms0.(ModSem.fnsems) ms1.(ModSem.fnsems);
    (* sim_initial_mrs: Forall2  *)
  }.

End SIMMODSEM.

