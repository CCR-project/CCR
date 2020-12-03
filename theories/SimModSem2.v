Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem.
Require Import Relation_Definitions.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{GRA: GRA.t}.
  Variable (ms0 ms1: ModSem.t).

  Let st_local: Type := ((string -> GRA) * GRA).

  Set Typeclasses Depth 5.
  Definition handle_rE_local `{eventE -< E}: rE ~> stateT st_local (itree E) :=
    fun _ e '(mrs, fr0) =>
    match e with
    | Put mn mr fr1 =>
      guarantee(URA.updatable (URA.add (mrs mn) fr0) (URA.add mr fr1));;
      Ret (((update mrs mn mr), fr1), tt)
    | MGet mn => Ret ((mrs, fr0), mrs mn)
    | FGet => Ret ((mrs, fr0), fr0)
    (* | Forge fr => Ret ((mrs, (URA.add hd fr) :: tl), tt) *)
    (* | Discard fr => *)
    (*   rest <- trigger (Choose _);; *)
    (*   guarantee(hd = URA.add fr rest);; *)
    (*   Ret ((mrs, rest :: tl), tt) *)
    (* | CheckWf mn => *)
    (*   assume(URA.wf (URA.add (mrs mn) hd));; *)
    (*   Ret ((mrs, frs), tt) *)
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

  Variable SR: relation st_local.

  (* Variable sim_itree: nat -> forall T, relation (itree (callE +' eventE) T). *)
  Variable sim_itree: forall T, nat -> relation (itree (callE +' eventE) T).
  Eval red in (stateT st_local (itree (callE +' eventE)) val).
  Let sim_ktree: nat -> relation (stateT st_local (itree (callE +' eventE)) val).
  Proof.
    intro n. r. intros k_src k_tgt.
    r in k_src. r in k_tgt.
    eapply respectful; cycle 2.
    { apply k_src. }
    { apply k_tgt. }
    { apply SR. }
    apply sim_itree. apply n.
  Defined.

  Let sim_fn: relation (list val -> itree Es val).
    eapply respectful.
    - r. eapply eq.
    - r. intros it_src it_tgt.
      apply interp_rE_local in it_src; cycle 1.
      { ss. }
      apply interp_rE_local in it_tgt; cycle 1.
      { ss. }
      apply (exists n, sim_ktree n it_src it_tgt).
  Defined.

  TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTt
  Check (SR ==> @sim_itree val)%signature.
  Inductive _sim_ktree sim_ktree:
    nat -> relation (stateT st_local (itree (callE +' eventE)) val) :=
  | sim_ktree_ret
      i0
    :
      _sim_ktree sim_ktree 
  .

  Let sim_bobo: nat -> relation (stateT st_local (itree (callE +' eventE)) val).
    i. r. intros k_src k_tgt. r in k_src. r in k_tgt.
  Defined.
  Variable sim_bobo: nat -> relation (stateT st_local (itree (callE +' eventE)) val).

  Let sim_fn: relation (list val -> itree Es val).
    eapply respectful.
    - r. eapply eq.
    - r. intros it_src it_tgt.
      apply bobo in it_src; cycle 1.
      { ss. }
      apply bobo in it_tgt; cycle 1.
      { ss. }
      apply (exists n, sim_bobo n it_src it_tgt).
  Defined.

  (*** can we give simulation relation for stateT st_local (itree (D +' E))?? ***)

  Check (State.interp_state (case_ (case_ State.pure_state handle_rE_local) State.pure_state) fn).
  Let anyhow_rE_erased (fn: (list val -> itree Es val))
    (* : (list val -> itree (callE +' eventE) val) *)
    :=
    fun varg => State.interp_state (case_ State.pure_state
                                          (case_ handle_rE_local State.pure_state)) (fn varg)
  .
  Definition interp_rE `{eventE -< E}: itree (rE +' E) ~> stateT r_state (itree E) :=
    State.interp_state (case_ handle_rE State.pure_state).
