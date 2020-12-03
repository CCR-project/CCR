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

From ITree Require Import
     Events.MapDefault.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Generalizable Variables E R A B C X Y K V.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section RelList.
  Variable A: Type.
  Variable R: relation A.
  Definition RelList: relation (list A) := Forall2 R.
End RelList.

Print Map_alist.
Print function_Map. (*** TODO: use Dec. Move to proper place ***)

Global Instance Dec_RelDec K `{Dec K}: @RelDec K eq :=
  { rel_dec := dec }.

Global Instance Dec_RelDec_Correct K `{Dec K}: RelDec_Correct Dec_RelDec.
Proof.
  unfold Dec_RelDec. ss.
  econs. ii. ss. unfold Dec_RelDec. split; ii.
  - unfold rel_dec in *. unfold sumbool_to_bool in *. des_ifs.
  - unfold rel_dec in *. unfold sumbool_to_bool in *. des_ifs.
Qed.



Section SIM.

  Context `{GRA: GRA.t}.

  (* Let st_local: Type := (list (string * GRA) * GRA). *)
  Let st_local: Type := ((alist string GRA) * GRA).

  Variable R: relation (alist string GRA).

  Set Typeclasses Depth 5.
  (**** It does not correctly handle module-resource.
        It should permit interference, but it doesn't.
   ****)
  Definition handle_rE_local `{eventE -< E}: rE ~> stateT st_local (itree E) :=
    fun _ e '(mrs, fr0) =>
    match e with
    | Put mn mr1 fr1 =>
      mr0 <- (Maps.lookup mn mrs)?;;
      guarantee(URA.updatable (URA.add mr0 fr0) (URA.add mr1 fr1));;
      Ret (((Maps.add mn mr1 mrs), fr1), tt)
    | MGet mn =>
      mr0 <- (Maps.lookup mn mrs)?;;
      Ret ((mrs, fr0), mr0)
    | FGet => Ret ((mrs, fr0), fr0)
    | Forge rarg => Ret ((mrs, URA.add fr0 rarg), tt)
    | Discard rret =>
      fr1 <- trigger (Choose _);;
      guarantee(fr0 = URA.add fr1 rret);;
      Ret ((mrs, fr1), tt)
    | CheckWf mn =>
      mr0 <- (Maps.lookup mn mrs)?;;
      assume(URA.wf (URA.add mr0 fr0));;
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

