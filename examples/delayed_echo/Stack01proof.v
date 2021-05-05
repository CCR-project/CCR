Require Import Mem1.
Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import HoareDef Stack0 Stack1 SimModSem.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import HTactics TODOYJ YPM.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.

Require Import Red.




(* Use the hint facility to implement a database mapping terms to terms. To declare a new database, use a definition: Definition mydatabase := True. *)
(* Then, to map mykey to myvalue, write the hint: Hint Extern 1 (Register mydatabase mykey) ⇒ Provide myvalue. *)
(* Finally, to query the value associated with a key, run the tactic ltac_database_get mydatabase mykey. This will leave at the head of the goal the term myvalue. It can then be named and exploited using intro. *)

Inductive Boxer : Type :=
  | boxer : forall (A:Type), A -> Boxer.
Inductive Ltac_database_token : Prop := ltac_database_token.
Definition ltac_database (D:Boxer) (T:Boxer) (A:Boxer) := Ltac_database_token.
Notation "'Register' D T" := (ltac_database (boxer D) (boxer T) _)
  (at level 69, D at level 0, T at level 0).
Lemma ltac_database_provide : forall (A:Boxer) (D:Boxer) (T:Boxer), ltac_database D T A.
Proof using. split. Qed.
Ltac Provide T := apply (@ltac_database_provide (boxer T)).
Ltac ltac_database_get D T :=
  let A := fresh "TEMP" in evar (A:Boxer);
  let H := fresh "TEMP" in
  assert (H : ltac_database (boxer D) (boxer T) A);
  [ subst A; auto
  | subst A; match type of H with
             | ltac_database _ _ (boxer ?L) =>
               let RES := fresh "TEMP" in
               pose L as RES; revert RES
             end;
    clear H ].

(* Ltac ltac_database_get_constr D T := *)
(*   ltac_database_get D T; *)
(*   match goal with *)
(*   | [ |- let _ := ?x in _ ] => constr:(x) *)
(*   end *)
(* . *)

(* Ltac _ltac_database_get_constr D T k := *)
(*   let A := fresh "TEMP" in evar (A:Boxer); *)
(*   let H := fresh "TEMP" in *)
(*   assert (H : ltac_database (boxer D) (boxer T) A); *)
(*   [ subst A; auto *)
(*   | subst A; match type of H with *)
(*              | ltac_database _ _ (boxer ?L) => *)
(*                k L *)
(*              end; *)
(*     clear H ]. *)

(*** See: http://adam.chlipala.net/cpdt/html/Match.html , "Error: variable n should be bound to a term." ***)


Module TEST.
Definition mydb0 := True.
Definition mydb1 := True.
Hint Extern 1 (Register mydb0 0) => Provide interp_bind.
Hint Extern 1 (Register mydb1 0) => Provide interp_tgt_bind.

Goal False.
  ltac_database_get mydb0 0. intro T; clearbody T.
  ltac_database_get mydb1 0. i.


  ltac_database_get mydb1 0.
  let tmp := match goal with
             | [ |- let _ := ?x in _ ] => constr:(x)
             end in pose tmp.
  (* ltac_database_get_constr mydb1 0 ltac:(fun H => pose H). *)
  (* let tmp := ltac_database_get_constr mydb1 0 in pose tmp. *)



  (* let A := fresh "TEMP" in evar (A:Boxer); *)
  (* let H := fresh "TEMP" in *)
  (* assert (H : ltac_database (boxer mydb0) (boxer 0) A). *)
  (* { Set Printing All. subst TEMP. debug eauto. } *)
  (* Unset Printing All. *)
  (* subst TEMP. *)
  (* match type of TEMP0 with *)
  (* | ltac_database _ _ (boxer ?L) => *)
  (*   (* generalize L *) *)
  (*   pose L *)
  (* end. *)
  (* clear TEMP0. *)
Abort.

End TEST.
Reset TEST.
(* Note for a possible alternative implementation of the ltac_database_token:
   Inductive Ltac_database : Type :=
     | ltac_database : forall A, A -> Ltac_database.
   Implicit Arguments ltac_database A.
*)






(* Hint Extern 1 (interp_hCallE_tgt _ _ _ = _) => pose "A". *)
(* Hint Extern 1 ((interp_hCallE_tgt _ _ _) >>= _ = _) => pose "A". *)
Definition namedb := True.
Hint Extern 1 (Register namedb @interp_hCallE_tgt) => Provide "interp_hCallE_tgt".
Hint Extern 1 (Register namedb ("interp_hCallE_tgt", "bind")) => Provide interp_tgt_bind.


Ltac get_head term :=
  match term with
  | ?f ?x => get_head f
  | _ => term
  end
.

Ltac get_tail term :=
  match term with
  (* | ?f _ _ _ ?x => get_tail x *)
  (* | ?f _ _ ?x => get_tail x *)
  (* | ?f _ ?x => get_tail x *)
  (* | ?f ?x => get_tail x *)

  (* | ?f ?x => x *)
  (* | _ => constr:(term) *)

  | ?f ?x => x
  end
.

Goal forall (f: nat -> nat -> nat -> nat -> Prop), f 0 1 2 3 -> False.
Proof.
  i.
  let tmp := (get_head (f 0 1 2 3)) in pose tmp as X.
  let tmp := (get_tail (f 0 1 2 3)) in pose tmp as Y.
  assert(X = f) by refl.
  assert(Y = 3) by refl.
Abort.

Goal forall {Σ : GRA.t} (stb : list (string * fspec)) (o : ord) [R S R_src : Type] (s : itree (hCallE +' pE +' eventE) R)
  (k : R -> itree (hCallE +' pE +' eventE) S) (h : S -> itree Es R_src),
` x : _ <- interp_hCallE_tgt stb o (` x : _ <- s;; k x);; h x =
` r : R <- interp_hCallE_tgt stb o s;; ` x : _ <- interp_hCallE_tgt stb o (k r);; h x.
  i.
  match goal with
  | [ |- ?itr >>= _ = _ ] => let interp := (get_head itr) in ltac_database_get namedb interp
  | [ |- ?itr = _ ] => let interp := (get_head itr) in ltac_database_get namedb interp
  end.
  ltac_database_get namedb ("interp_hCallE_tgt", "bind"); intro tmp; clearbody tmp. rewrite tmp. ss.
Qed.






Ltac _red_itree f :=
  match goal with
  | [ |- ITree.bind' _ ?itr = _] =>
    match itr with
    | ITree.bind' _ _ =>
      instantiate (f:=_continue); apply bind_bind; fail
    | Tau _ =>
      instantiate (f:=_break); apply bind_tau; fail
    | Ret _ =>
      instantiate (f:=_continue); apply bind_ret_l; fail
    | _ =>
      fail
    end
  | [ |- trigger _ = _] =>
    instantiate (f:=_break); apply bind_ret_r_rev; fail
  | _ => fail
  end.

Ltac _red_interp f :=
  match goal with
  | [ |- ITree.bind' _ ?term = _ ] =>
    let my_interp := get_head term in
    ltac_database_get namedb my_interp;
    let itr := get_tail term in
    match itr with
    | ITree.bind' _ _ =>
      let lemma := ltac_database_get namedb (my_interp, "bind") in
      instantiate (f:=_continue); eapply lemma; fail
    | Tau _ =>
      instantiate (f:=_break); apply interp_tgt_tau; fail
    | Ret _ =>
      instantiate (f:=_continue); apply interp_tgt_ret; fail
    | trigger ?e =>
      instantiate (f:=_break);
      match (type of e) with
      | context[hCallE] => apply interp_tgt_hcall
      | context[eventE] => apply interp_tgt_triggere
      | context[pE] => apply interp_tgt_triggerp
      | _ => fail 2
      end
    | triggerUB =>
      instantiate (f:=_break); apply interp_tgt_triggerUB; fail
    | triggerNB =>
      instantiate (f:=_break); apply interp_tgt_triggerNB; fail
    | unwrapU _ =>
      instantiate (f:=_break); apply interp_tgt_unwrapU; fail
    | unwrapN _ =>
      instantiate (f:=_break); apply interp_tgt_unwrapN; fail
    | assume _ =>
      instantiate (f:=_break); apply interp_tgt_assume; fail
    | guarantee _ =>
      instantiate (f:=_break); apply interp_tgt_guarantee; fail
    | _ =>
      fail
    end
  | [ |- interp_hCallE_tgt _ _ _ = _] =>
    instantiate (f:=_continue); apply bind_ret_r_rev; fail
  end
.

Ltac _red_interp_tgt f :=
  match goal with
  | [ |- ITree.bind' _ (interp_hCallE_tgt _ _ ?itr) = _ ] =>
    match itr with
    | ITree.bind' _ _ =>
      instantiate (f:=_continue); eapply interp_tgt_bind; fail
    | Tau _ =>
      instantiate (f:=_break); apply interp_tgt_tau; fail
    | Ret _ =>
      instantiate (f:=_continue); apply interp_tgt_ret; fail
    | trigger ?e =>
      instantiate (f:=_break);
      match (type of e) with
      | context[hCallE] => apply interp_tgt_hcall
      | context[eventE] => apply interp_tgt_triggere
      | context[pE] => apply interp_tgt_triggerp
      | _ => fail 2
      end
    | triggerUB =>
      instantiate (f:=_break); apply interp_tgt_triggerUB; fail
    | triggerNB =>
      instantiate (f:=_break); apply interp_tgt_triggerNB; fail
    | unwrapU _ =>
      instantiate (f:=_break); apply interp_tgt_unwrapU; fail
    | unwrapN _ =>
      instantiate (f:=_break); apply interp_tgt_unwrapN; fail
    | assume _ =>
      instantiate (f:=_break); apply interp_tgt_assume; fail
    | guarantee _ =>
      instantiate (f:=_break); apply interp_tgt_guarantee; fail
    | _ =>
      fail
    end
  | [ |- interp_hCallE_tgt _ _ _ = _] =>
    instantiate (f:=_continue); apply bind_ret_r_rev; fail
  | _ => fail
  end.

Ltac _red_lsim f :=
  _red_interp f || _red_itree f || fail.

Ltac ired_l := try (prw _red_lsim 2 1 0).
Ltac ired_r := try (prw _red_lsim 1 1 0).

Ltac ired_both := ired_l; ired_r.

Ltac prep := ired_both.

Ltac _step :=
  match goal with
  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, trigger (Choose _) >>= _) (_, ?i_tgt)) ] => idtac *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_both; force_l; ss; fail]
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    ired_both; gstep; eapply sim_itree_take_src; [eapply OrdArith.lt_from_nat; apply Nat.lt_succ_diag_r|]; intro name

  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_both; force_r; ss; fail]
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    ired_both; gstep; eapply sim_itree_choose_tgt; [eapply OrdArith.lt_from_nat; apply Nat.lt_succ_diag_r|]; intro name



  | _ => (*** default ***)
    gstep; eapply safe_sim_sim; econs; try (eapply OrdArith.lt_from_nat; apply Nat.lt_succ_diag_r); i
  end;
  (* idtac *)
  match goal with
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end
.
Ltac steps := repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) unfold alist_add; simpl; des_ifs_safe).











Section AUX.
  Context `{Σ: GRA.t}.

  Lemma _Own_ε: Own ε = ⌜True⌝. Proof. apply func_ext; i. unfold Own. apply prop_ext. split; i; ss. r. esplit. rewrite URA.unit_idl; refl. Qed.
  Lemma Own_ε: ⌞Own ε⌟. Proof. iIntro. rewrite _Own_ε. ss. Fail Qed. Abort. (********** coq bug !!!!!!!!!!!!!!! **************)
  Lemma Own_ε: ⌞Own ε⌟. Proof. iIntro. exists r. r_solve. Qed.

  Lemma iHyp_update_r: forall P r0 r1, r0 = r1 -> iHyp P r0 -> iHyp P r1. Proof. i. subst. ss. Qed.
  Lemma unit_id': forall r0 (my_ε: Σ), my_ε = ε -> r0 ⋅ my_ε = r0. Proof. i. subst. r_solve. Qed.

End AUX.
Global Opaque _APC.

Ltac iImpure H :=
  let name := fresh "my_r" in
  specialize (H ε URA.wf_unit I); rewrite intro_iHyp in H;
  (* set (name:=ε); *) (*** <- it has side effect in goal ***)
  pose (name:=(@URA.unit (GRA.to_URA _)));
  eapply iHyp_update_r with (r1:=name) in H; [|refl];
  on_gwf ltac:(fun GWF => erewrite <- unit_id' with (my_ε:=name) in GWF; [|refl]);
  match goal with
  | [ |- (gpaco3 (SimModSem._sim_itree _) _ _ _ _ _  _) ] => idtac
  | [ |- iHyp _ _ ] => erewrite <- unit_id' with (my_ε:=name); [|refl]
  | _ => idtac
  end;
  clearbody name
.





Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).
  Eval compute in (@URA.car Mem1._memRA).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
        (<<SRC: mrps_src0 = (ε, tt↑)>>) /\
        (<<TGT: mrps_tgt0 = (ε, tt↑)>>)
  .

  Local Opaque points_to.

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.

  Theorem correct: ModSemPair.sim Stack1.StackSem Stack0.StackSem.
  Proof.
    econstructor 1 with (wf:=wf); et; swap 2 3.
    { ss. }

    econs; ss.
    { unfold popF. init.
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *. ss.
      iRefresh. do 4 iDestruct PRE. iMod A. iMod PRE. clarify.
      apply Any.upcast_inj in PRE. des; clarify. steps. rewrite Any.upcast_downcast in *. clarify. steps.

      unfold ccall. steps. astart 10.

      acall_tac __ __ (@URA.unit Σ) A0 A1; ss; et.
      { instantiate (2:= (_, _, _)). cbn. esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss; et. }
      { esplits; ss; et. eauto with ord_step. }
      ss. des; subst. rewrite Any.upcast_downcast. steps. iRefresh. iDestruct POST. iMod A. apply Any.upcast_inj in A; des; clarify.


      destruct l; ss.
      - iMod A0. subst.
        hexploit Own_ε; intro A. iImpure A.
        acall_tac __ __ (@URA.unit Σ) POST A; ss; et.
        { instantiate (2:= (_, _)). cbn. esplits; try refl; iRefresh. iSplitP; ss. iSplitR A; ss; et. right; iRefresh. rr. esplits; et. }
        { esplits; ss. eauto with ord_step. }
        ss. des; subst. rewrite Any.upcast_downcast. steps. iRefresh. iDestruct POST0. iMod A. apply Any.upcast_inj in A; des; clarify.
        clear POST0. steps.

        astop. force_l. eexists. hret_tac (@URA.unit Σ) POST; ss.
      - do 4 iDestruct A0. iMod A0. subst.
        rename n into rref. rename x6 into hd. rename x7 into next.
        rewrite points_to_split in A1. rewrite <- GRA.embed_add in A1. rewrite own_sep in A1. iDestruct A1. ss.
        acall_tac __ __ (@URA.unit Σ) (A, A0, POST) A1; ss; et.
        { instantiate (2:= (_, _)). cbn. esplits; try refl; iRefresh. iSplitP; ss. iSplitR A1; ss; et. do 4 left; do 3 eexists; iRefresh.
          iSplitP; ss. iSplitP; ss. }
        { esplits; ss. eauto with ord_step. }
        ss. des; subst. rewrite Any.upcast_downcast. steps. iRefresh. iDestruct POST0. iMod A1. apply Any.upcast_inj in A1; des; clarify.
        steps.

        acall_tac __ __ (@URA.unit Σ) (A0, A, POST) POST0; ss; et.
        { instantiate (2:=(_, _, _)). cbn. esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        ss. des; iRefresh. iDestruct POST1. iMod A1. apply Any.upcast_inj in A1. des; clarify. steps.


        acall_tac __ __ (@URA.unit Σ) (A, POST, POST1) A0; ss; et.
        { instantiate (2:=(_, _, _)). cbn. esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        ss. des; iRefresh. iDestruct POST0. iMod A0. apply Any.upcast_inj in A0. des; clarify. steps.
        rewrite Any.upcast_downcast in *. clarify.


        acall_tac __ __ (@URA.unit Σ) (A, POST, POST0) POST1; ss; et.
        { instantiate (2:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        des; iRefresh. subst. steps. rewrite Any.upcast_downcast in *. clarify.


        acall_tac __ __ (@URA.unit Σ) (A, POST) POST0; ss; et.
        { instantiate (2:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        des; iRefresh. subst. steps. rewrite Any.upcast_downcast in *. clarify.


        acall_tac __ __ (@URA.unit Σ) (A) POST; ss; et.
        { instantiate (2:=(_, _, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        ss. des; iRefresh. subst. steps. rewrite Any.upcast_downcast in *. clarify.

        astop. force_l. eexists.
        hret_tac (@URA.unit Σ) (POST0, A); ss.
        { esplits; try refl; iRefresh. iSplitP; ss. eexists; iRefresh. iSplitR A; et. }
    }
    econs; ss.
    { unfold pop2F. init.
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *. ss.
      iRefresh. do 4 iDestruct PRE. iDestruct A0. iMod A. iMod PRE. clarify.
      apply Any.upcast_inj in PRE. des; clarify. steps. rewrite Any.upcast_downcast in *. clarify. steps.

      unfold ccall. astart 10. steps.

      destruct l; ss.
      - iMod A1; subst.
        hexploit Own_ε; intro A. iImpure A.
        acall_tac __ __ (@URA.unit Σ) A0 A; ss; et.
        { instantiate (2:= (_, _)). cbn. esplits; try refl; iRefresh. iSplitP; ss. iSplitR A; ss; et. right; iRefresh. rr. esplits; et. }
        { esplits; ss. eauto with ord_step. }
        ss. des; subst. rewrite Any.upcast_downcast. steps. iRefresh. iDestruct POST. iMod A. apply Any.upcast_inj in A; des; clarify.
        clear POST. steps.

        astop. force_l. eexists.
        hret_tac (@URA.unit Σ) A0; ss.
      - do 4 iDestruct A1. iMod A1. subst.
        rename n into iref. rename x2 into unknown. rename x5 into hd. rename x6 into next. rename A2 into A1.

        rewrite points_to_split in A1. rewrite <- GRA.embed_add in A1. rewrite own_sep in A1. iDestruct A1. ss.
        acall_tac __ __ (@URA.unit Σ) (A, A0, A2) A1; ss; et.
        { instantiate (2:= (_, _)). cbn. esplits; try refl; iRefresh. iSplitP; ss. iSplitR A1; ss; et. do 4 left; do 3 eexists; iRefresh.
          iSplitP; ss. iSplitP; ss. }
        { esplits; ss. eauto with ord_step. }
        ss. des; subst. rewrite Any.upcast_downcast. steps. iRefresh. iDestruct POST. iMod A1. apply Any.upcast_inj in A1; des; clarify.
        steps.

        acall_tac __ __ (@URA.unit Σ) (A0, A, A2) POST; ss; et.
        { instantiate (2:=(_, _, _)). cbn. esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        ss. des; iRefresh. iDestruct POST0. iMod A1. apply Any.upcast_inj in A1. des; clarify. steps.


        acall_tac __ __ (@URA.unit Σ) (A, A0, POST0) A2; ss; et.
        { instantiate (2:=(_, _, _)). cbn. esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        ss. des; iRefresh. iDestruct POST. iMod A1. apply Any.upcast_inj in A1. des; clarify. steps.
        rewrite Any.upcast_downcast in *. clarify.


        acall_tac __ __ (@URA.unit Σ) (A, A0, POST) POST0; ss; et.
        { instantiate (2:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        des; iRefresh. subst. steps. rewrite Any.upcast_downcast in *. clarify.


        acall_tac __ __ (@URA.unit Σ) (A, A0) POST; ss; et.
        { instantiate (2:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        des; iRefresh. subst. steps. rewrite Any.upcast_downcast in *. clarify.


        acall_tac __ __ (@URA.unit Σ) (A) A0; ss; et.
        { instantiate (2:=(_, _, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. et. }
        { esplits; ss. eauto with ord_step. }
        ss. des; iRefresh. subst. steps. rewrite Any.upcast_downcast in *. clarify.

        astop. force_l. eexists.
        hret_tac (@URA.unit Σ) (POST, A); ss.
        { esplits; try refl; iRefresh. eexists; iRefresh. iSplitR POST; ss. iSplitP; ss. }
    }
    econs; ss.
    { unfold pushF. init.
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *. ss.
      iRefresh. do 3 iDestruct PRE. iMod A. iMod PRE. clarify.
      apply Any.upcast_inj in PRE. des; clarify. steps. rewrite Any.upcast_downcast in *. clarify. steps.

      unfold ccall. astart 10. steps.

      acall_tac __ __ (@URA.unit Σ) A0 (@URA.unit Σ); ss; et.
      { instantiate (2:=2). esplits; try refl; iRefresh. ss. }
      { esplits; ss. eauto with ord_step. }
      des; iRefresh. subst. do 2 iDestruct POST. iMod POST. rewrite Any.upcast_downcast. apply Any.upcast_inj in POST. des; clarify. steps.

      ss. rewrite points_to_split in A. rewrite <- GRA.embed_add in A. rewrite own_sep in A. iDestruct A. ss.

      acall_tac __ __ (@URA.unit Σ) (A0, A1) A; ss; et.
      { instantiate (2:=(_, _, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitR A; ss. et. }
      { esplits; ss. eauto with ord_step. }
      ss. des; iRefresh. subst. rewrite Any.upcast_downcast. steps.

      acall_tac __ __ (@URA.unit Σ) (A0, POST) A1; ss; et.
      { instantiate (2:=(_, _, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitR A1; ss. et. }
      { esplits; ss. eauto with ord_step. }
      ss. des; iRefresh. subst. rewrite Any.upcast_downcast. steps.

      astop. force_l. eexists.
      hret_tac (@URA.unit Σ) (A0, POST, POST0); ss.
      { esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. do 2 eexists; iRefresh. iSplitR A0; et. iSplitP; ss; et.
        rewrite points_to_split. rewrite <- GRA.embed_add. rewrite own_sep. iSplitL POST; ss.
      }
    }
  Qed.

End SIMMODSEM.
