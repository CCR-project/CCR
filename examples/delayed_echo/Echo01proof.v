Require Import LinkedList1 Client1 Mem1 Mem2.
Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import HoareDef Echo0 Echo1 SimModSem.

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

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



Ltac r_inb r rs :=
  match rs with
  | r => constr:(true)
  | (r ⋅ ?y) => constr:(true)
  | (?x ⋅ r) => constr:(true)
  | (?x ⋅ ?y) =>
    let tmp0 := r_inb r x in
    let tmp1 := r_inb r y in
    let tmp := eval simpl in (tmp0 || tmp1) in
        (* let tmp := (tmp0 || tmp1) in *)
        constr:(tmp)
  | _ => constr:(false)
  end.

Ltac r_subtract xs ys :=
  match xs with
  (* | ?x => tryif r_in x ys then constr:(ε) else constr:(x) *)
  | (?xs0 ⋅ ?xs1) =>
    let tmp0 := (r_subtract xs0 ys) in
    let tmp1 := (r_subtract xs1 ys) in
    (* let tmp0 := xs0 in *)
    (* let tmp1 := xs1 in *)
    constr:(tmp0 ⋅ tmp1)
  (* | ?y => (tryif idtac then constr:(ε) else constr:(ε)) *)
  (* | ?y => let tmp := (tryif idtac then constr:(ε) else constr:(ε)) in constr:(tmp) *)
  (* | ?y => constr:(ε) || constr:(ε) *)
  (* | ?y => constr:(if ltac:(r_in y ys) then ε else ε) *)
  (* | ?y => first[constr:(ε)|constr:(ε)] *)
  (* | ?y => constr:(ε) *)
  (* | ?y => constr:(if true then ε else ε) *)
  (* | ?y => let tmp := tryif r_in y ys then constr:(true) else constr:(false) in *)
  (*         constr:(if tmp then ε else ε) *)
  (* | ?y => y *)
  (* | ?y => (r_in y ys; constr:(ε)) + y *)
  | ?y => let tmp := (r_inb y ys) in
          let tmp := constr:(if tmp then ε else y) in
          let tmp := eval simpl in tmp in
              constr:(tmp)
  end
.

Ltac r_clearε rs :=
  match rs with
  | (ε ⋅ ?rs) => let tmp := r_clearε rs in constr:(tmp)
  | (?rs ⋅ ε) => let tmp := r_clearε rs in constr:(tmp)
  | (?rs0 ⋅ ?rs1) =>
    let tmp0 := (r_clearε rs0) in
    let tmp1 := (r_clearε rs1) in
    match tmp0 with
    | ε =>
      match tmp1 with
      | ε => fail 3
      | _ => constr:(tmp1)
      end
    | _ =>
      match tmp1 with
      | ε => constr:(tmp0)
      | _ => constr:(tmp0 ⋅ tmp1)
      end
    end
  | ?r => constr:(r)
  end
.

Ltac r_equalize :=
  match goal with
  | [ |- ?lhs = ?rhs ] =>
    let tmp0 := (r_subtract rhs lhs) in
    let tmp1 := r_clearε tmp0 in
    instantiate (1:=tmp1)
  | [ |- URA.extends ?lhs ?rhs ] =>
    let tmp0 := (r_subtract rhs lhs) in
    let tmp1 := r_clearε tmp0 in
    exists tmp1
  (*** match does not work ***)
  (* | [ |- exists _, ?lhs = ?rhs ] => *)
  (*   let tmp := (r_subtract rhs lhs) in *)
  (*   let tmp := r_clearε tmp in *)
  (*   exists tmp *)
  end.

Ltac r_first rs :=
  match rs with
  | (?rs0 ⋅ ?rs1) =>
    let tmp0 := r_first rs0 in
    constr:(tmp0)
  | ?r => constr:(r)
  end
.

(* Ltac r_solver := *)
(*   repeat rewrite <- URA.add_assoc; *)
(*   match goal with *)
(*   (* | [|- (?a ⋅ _) = _ ] => *) *)
(*   (*   repeat (rewrite <- (URA.add_comm a); repeat rewrite URA.add_assoc) *) *)
(*   | [|- (?a ⋅ _) = _ ] => *)
(*     idtac a; *)
(*     repeat rewrite ! URA.add_assoc; *)
(*     rewrite <- (URA.add_comm a); *)
(*     repeat rewrite ! URA.add_assoc; *)
(*     idtac *)
(*     (* repeat (rewrite <- (URA.add_comm a); repeat rewrite URA.add_assoc) *) *)
(*   | [|- ?lhs = ?rhs ] => reflexivity *)
(*   end *)
(* . *)
Ltac r_solve :=
  repeat rewrite URA.add_assoc;
  repeat (try rewrite URA.unit_id; try rewrite URA.unit_idl);
  match goal with
  | [|- ?lhs = (_ ⋅ _) ] =>
    let a := r_first lhs in
    try rewrite <- (URA.add_comm a);
    repeat rewrite <- URA.add_assoc;
    f_equal;
    r_solve
  | _ => reflexivity
  end
.





Section SOLVER.
  Context {Σ: GRA.t}.
  Variables a b c d e f: Σ.

  Goal False.
    let tmp := r_clearε (ε ⋅ ε ⋅ (b ⋅ a) ⋅ ε ⋅ e) in pose tmp as c0.
    assert(c0 = (b ⋅ a) ⋅ e) by reflexivity.
    Fail let tmp := r_clearε ((ε ⋅ ε) ⋅ (ε ⋅ ε)) in pose tmp.
    let tmp := r_clearε ((ε ⋅ (ε ⋅ ε) ⋅ ε) ⋅ (b ⋅ a) ⋅ ε ⋅ e) in pose tmp as c1.
    assert(c1 = (b ⋅ a) ⋅ e) by reflexivity.
    let tmp := r_clearε ((ε ⋅ ε) ⋅ b ⋅ (ε ⋅ ε) ⋅ a ⋅ ε ⋅ e) in pose tmp as c2.
    assert(c2 = (b ⋅ a) ⋅ e) by reflexivity.
  Abort.

  Goal exists x, a ⋅ b = a ⋅ x. eexists. Fail r_equalize. symmetry. r_equalize; r_solve. Qed.
  Goal exists x, b ⋅ a = a ⋅ x. eexists. Fail r_equalize. symmetry. r_equalize; r_solve. Qed.
  Goal exists x, a ⋅ b = x ⋅ a. eexists. Fail r_equalize. symmetry. r_equalize; r_solve. Qed.
  Goal exists x, b ⋅ a = x ⋅ a. eexists. Fail r_equalize. symmetry. r_equalize; r_solve. Qed.
  Goal exists x, a = x. eexists. Fail r_equalize. symmetry. r_equalize; r_solve. Qed.

  Goal URA.extends (d) (c ⋅ b ⋅ a ⋅ d ⋅ e).
  Proof. r_equalize. r_solve. Qed.

  Goal URA.extends (d) (c ⋅ (b ⋅ a) ⋅ d ⋅ e).
  Proof. r_equalize. r_solve. Qed.

  Goal URA.extends (d ⋅ c ⋅ ε) (ε ⋅ c ⋅ (b ⋅ a) ⋅ d ⋅ e).
  Proof. r_equalize. r_solve. Qed.

  Goal URA.extends (b ⋅ d ⋅ (c ⋅ a) ⋅ e) (a ⋅ ε ⋅ c ⋅ ε ⋅ (b ⋅ ε) ⋅ e ⋅ ε ⋅ d).
  Proof. r_equalize. r_solve. Qed.

  Goal a ⋅ b ⋅ (c ⋅ (d ⋅ e)) = a ⋅ c ⋅ (ε ⋅ (b ⋅ d ⋅ e)).
  Proof. r_solve. Qed.

End SOLVER.


















(******** TODO : remove redundancy with LL01proof ***********)
Definition __gwf_mark__ (* (is_src: bool) *) (P: Prop): Prop := P.
Lemma gwf_mark_spec: forall P, P <-> __gwf_mark__ P. refl. Qed.
(* Opaque __gwf_mark__. *)
Notation "'☀'" := (__gwf_mark__ _) (at level 60).



(* Ltac iCheckWf := *)
(*   tryif (match goal with | [WF0: URA.wf _, WF1: URA.wf _ |- _ ] => idtac end) then fail 1 else idtac *)
(* . *)

(* Ltac iClears' := *)
(*   match goal with *)
(*   | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (([(_, (?src0, _))], ?src1), ?src2) (([(_, (?tgt0, _))], ?tgt1), ?tgt2)) ] => *)
(*     let name := fresh "tmp" in *)
(*     let all := constr:(src0 ⋅ src1 ⋅ tgt0 ⋅ tgt1) in *)
(*     pose all as name; *)
(*     repeat multimatch goal with *)
(*            | [WF: URA.wf ?rh |- _ ] => tryif r_contains rh all then idtac else clear WF *)
(*            | [H: iHyp ?ph ?rh |- _ ] => *)
(*              tryif r_contains rh all then idtac else clear H *)
(*                                                            (* idtac H; *) *)
(*                                                            (*   idtac rh; *) *)
(*                                                            (*   tryif r_contains rh all then idtac "CONTAINS" else idtac "DROP" *) *)
(*            end; *)
(*     clear name *)
(*   end; *)
(*   iCheckWf *)
(* . *)
Ltac iCheckWf :=
  (* tryif (match goal with | [WF0: __gwf_mark__ (URA.wf _), WF1: __gwf_mark__ (URA.wf _) |- _ ] => idtac end) then fail 1 else idtac *)
  tryif (match goal with | [WF0: context[(URA.wf _)], WF1: context[(URA.wf _)] |- _ ] => idtac end) then fail 1 else idtac
.

Ltac iClears' :=
  match goal with
  | [ WF: __gwf_mark__ (URA.wf ?rs) |- _ ] =>
    repeat multimatch goal with
           | [H: iHyp ?ph ?rh |- _ ] =>
             tryif r_contains rh rs then idtac else clear H
           end
  end;
  iCheckWf.

Ltac iRefresh :=
  clear_bar;
  bar;
  repeat multimatch goal with
         | [H: URA.extends ?a ?b |- _ ] => replace (URA.extends a b) with ((Own a) b) in H by reflexivity
         | [H: iHyp _ _ |- _ ] => revert H
         (*** TODO: move existing resources to top ***)
         (*** TODO: remove redundant URA.wf ***)
         | [H: ?ip ?r |- _ ] =>
           match type of ip with
           | iProp => rewrite intro_iHyp in H; move r at top; move H at bottom
           | _ => idtac
           end
         end;
  i;
  try (match goal with
       | [ |- ?ip ?r ] =>
         match type of ip with
         | iProp => rewrite intro_iHyp
         | _ => idtac
         end
       end;
       iClears;
       iClears')
.

Ltac iSplitP :=
  match goal with
  | |- ᐸ (Pure ?ph) ** ?pg ᐳ =>
    erewrite f_equal; cycle 1; [ instantiate (1 := (ε ⋅ _)); rewrite URA.unit_idl; refl | eapply sepconj_merge; iClears ]
  | |- ᐸ ?ph ** (Pure ?pg) ᐳ =>
    erewrite f_equal; cycle 1; [ instantiate (1 := (_ ⋅ ε)); rewrite URA.unit_id; refl | eapply sepconj_merge; iClears ]
  end
.

Ltac iDestruct' H :=
  match type of H with
  | iHyp (Exists _, _) _ => destruct H as [? H]; iRefresh
  | iHyp (_ ** _) _ =>
    let name0 := fresh "A" in
    apply sepconj_split in H as [? [? [H [name0 ?]]]]; subst; iRefresh
  end.

Ltac iSplitL Hs0 :=
  match goal with
  | |- ᐸ ?ph ** ?pg ᐳ =>
    let tmp := (r_gather Hs0) in
    erewrite f_equal; cycle 1; [instantiate (1 := tmp ⋅ _)|eapply sepconj_merge; [iClears|(*** TODO: We don't use iClears here because there are unresolved existentials.
                                                             use pcm solver and put iClears ***)]]
  end.
Ltac iSplitR Hs0 :=
  match goal with
  | |- ᐸ ?ph ** ?pg ᐳ =>
    let tmp := (r_gather Hs0) in
    erewrite f_equal; cycle 1; [instantiate (1 := _ ⋅ tmp)|eapply sepconj_merge; [(*** TODO: We don't use iClears here because there are unresolved existentials.
                                                             use pcm solver and put iClears ***)|iClears]]
  end.

Ltac iExists' Hs := let rs := r_gather Hs in exists rs.







Require Import HTactics.
Ltac harg_tac :=
  HTactics.harg_tac;
  match goal with
  | [H: URA.wf _ |- _] => rewrite (gwf_mark_spec) in H
  end.






Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.
  Context `{@GRA.inG Echo1.echoRA Σ}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).
  Eval compute in (@URA.car Mem1._memRA).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mr: Σ) (ll: val),
        (<<SRC: mrps_src0 = Maps.add "Echo" (mr, tt↑) Maps.empty>>) /\
        (<<TGT: mrps_tgt0 = Maps.add "Echo" (ε, ll↑) Maps.empty>>) /\
        (* (<<SIM: (iHyp (⌜ll = Vnullptr⌝ ∨ (Exists ns, (Own(GRA.padding(echo_black ns))) ** is_list ll (List.map Vint ns))) mr)>>) *)
        (* (<<SIM: (iHyp (Exists ns, (Own(GRA.padding(echo_black ns))) *)
        (*                             ** (is_list ll (List.map Vint ns) ∨ (Own(GRA.padding(echo_white ns))))) mr)>>) *)
        (<<SIM: (iHyp (Exists ns, ((Own(GRA.padding(echo_black ns))) ** is_list ll (List.map Vint ns)) ∨ (Own(GRA.padding(echo_white ns)))) mr)>>)
  .

  Local Opaque is_list.

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.


  Lemma unfold_APC: forall n, _APC n =
    match n with
    | 0 => Ret tt
    | S n => break <- trigger (Choose _);;
             if break: bool
             then Ret tt
             else '(fn, varg) <- trigger (Choose _);;
                  trigger (hCall true fn varg);; _APC n
    end.
    { i. destruct n; ss. }
  Qed.
  Opaque _APC.

  Lemma unfold_is_list: forall ll xs, is_list ll xs = 
    match xs with
    | [] => ⌜ll = Vnullptr⌝
    | xhd :: xtl =>
      Exists lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (Own (GRA.padding ((lhd,0%Z) |-> [xhd; ltl])))
                                 ** is_list ltl xtl
    end
  .
    { i. destruct xs; ss. }
  Qed.

  Lemma Own_downward: forall r a0 a1, iHyp (Own r) a0 -> URA.extends a0 a1 -> iHyp (Own r) a1.
  Proof. i. eapply Own_extends; et. Qed.

  (* Lemma is_list_downward: forall ll xs a0 a1, iHyp (is_list ll xs) a0 -> URA.extends a0 a1 -> iHyp (is_list ll xs) a1. *)
  (* Proof. *)
  (*   admit "ez". *)
  (* Qed. *)

  Lemma wf_downward: forall (r0 r1: Σ) (EXT: URA.extends r0 r1), URA.wf r1 -> URA.wf r0.
  Proof.
    i. rr in EXT. des; subst. eapply URA.wf_mon; et.
  Qed.




  Ltac iOwnWf G :=
    match goal with
    | H:iHyp (Own ?r) ?rh |- _ =>
      check_equal H G;
      let name := fresh "WF" in
      assert(name: URA.wf r); [eapply wf_downward; [eapply H|eapply wf_downward; et; r_equalize; r_solve]|]
    end.

  Ltac until_bar TAC :=
    (on_last_hyp ltac:(fun id' =>
                         match type of id' with
                         | IPROPS => intros
                         | _ => TAC id'; revert id'; until_bar TAC
                         end)).
  Ltac rr_until_bar := until_bar ltac:(fun H => rr in H).

  Opaque points_to.

  Lemma own_update: forall (x y: Σ) rx ctx, URA.updatable x y -> iHyp (Own x) rx -> URA.wf (rx ⋅ ctx) ->
                                                   (* exists ry, iHyp (Own y) ry /\ URA.wf (ry ⋅ ctx) /\ URA.updatable rx ry. *)
                                                   exists ry, iHyp (Own y) ry /\ URA.wf (ry ⋅ ctx) /\ URA.updatable (rx ⋅ ctx) (ry ⋅ ctx).
  Proof.
    { clear_until Σ. i. dup H. rr in H0. destruct H0; clear H0. subst. r in H.
      specialize (H (x0 ⋅ ctx)). rewrite ! URA.add_assoc in H. spc H.
      exists (y ⋅ x0). esplits; et.
      - rr. esplits; et.
      - eapply URA.updatable_add; try refl. eapply URA.updatable_add; try refl. et.
    }
  Qed.

  Ltac on_wf TAC := match goal with | WF:☀ |- _ => TAC WF end.





  Theorem correct: ModSemPair.sim Echo1.EchoSem Echo0.EchoSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. unfold alist_add; cbn. esplits; ss; eauto. eexists nil; ss; iRefresh.
      rewrite unfold_is_list. left. eexists _, ε. split; ss.
      { rewrite URA.unit_id; ss. }
      split; ss. refl.
    }

    Opaque URA.add.
    econs; ss.
    { unfold echoF, echo_body. init. harg_tac.
      iRefresh. do 2 iDestruct PRE. iPure A. iPure A0. clarify.
      iDestruct SIM.
      destruct SIM as [A|A]; iRefresh; cycle 1.
      { exfalso. iMerge A PRE. rewrite <- own_sep in A. rewrite GRA.padding_add in A.
        iOwnWf A. clear - WF. apply GRA.padding_wf in WF. des. ss.
      }

      iDestruct A. subst.
      rename x into ns. rename x0 into ns0.
      assert(ns = ns0).
      { iMerge A PRE. rewrite <- own_sep in A. rewrite GRA.padding_add in A.
        iOwnWf A. eapply GRA.padding_wf in WF. des. eapply URA.auth_included in WF. des.
        clear - WF.
        Local Transparent URA.add.
        rr in WF. des. ss. des_ifs.
        Local Opaque URA.add.
      }
      subst.




      steps. unfold hcall, ccall. steps.
      unfold body_to_tgt. unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
      Inductive ltac_Wild : Set :=
      | ltac_wild : ltac_Wild.
      Notation "'__'" := ltac_wild : ltac_scope.
      Open Scope ltac_scope.
      
      Ltac r_gather Hs :=
        match Hs with
        | (?H0, ?H1) => let rs0 := r_gather H0 in
                        let rs1 := r_gather H1 in
                        constr:((rs0 ⋅ rs1))
        | ?H => match type of H with
                | iHyp _ ?rh => constr:(rh)
                | _ => H
                end
        end.
      Ltac hcall_tac x o MR_SRC1 FR_SRC1 RARG_SRC :=
        let mr_src1 := r_gather MR_SRC1 in
        let fr_src1 := r_gather FR_SRC1 in
        let rarg_src := r_gather RARG_SRC in
        let tac0 := first [eapply URA.extends_updatable; r_equalize; r_solve (*** normal case ***)
                          |rewrite ! URA.add_assoc in *; etrans; eauto; eapply URA.extends_updatable; r_equalize; r_solve
(*** we have updatable in premise; TODO: do it better ***)] in
        let tac1 := (on_wf ltac:(fun H => clear H);
                     let WF := fresh "WF" in
                     intros ? ? ? ? ? WF; cbn in WF; desH WF; subst;
                     esplits; ss; et; i; rewrite gwf_mark_spec with (P:=URA.wf _) in *; iRefresh; iClears') in
        prep;
        match x with
        | ltac_wild =>
          match o with
          | ltac_wild => eapply (hcall_clo _ (mr_src1:=mr_src1) (fr_src1:=fr_src1) (rarg_src:=rarg_src)); [tac0|lia|..|tac1]
          | _ => eapply (hcall_clo _ (o:=o) (mr_src1:=mr_src1) (fr_src1:=fr_src1) (rarg_src:=rarg_src)); [tac0|lia|..|tac1]
          end
        | _ => eapply (hcall_clo x (o:=o) (mr_src1:=mr_src1) (fr_src1:=fr_src1) (rarg_src:=rarg_src)); [tac0|lia|..|tac1]
        end
      .
      hcall_tac __ __ (A, A0) PRE (@URA.unit Σ); ss; et.
      { esplits; ss; et. eexists; iRefresh. left; iRefresh. iSplitL A; ss.
        - iApply A; ss.
        - iApply A0; ss.
      }
      des; subst. rewrite Any.upcast_downcast. steps. rewrite Any.upcast_downcast. steps.



      iDestruct SIM. destruct SIM as [SIM|SIM]; iRefresh; cycle 1.
      { exfalso. iMerge SIM PRE. rewrite <- own_sep in SIM. rewrite GRA.padding_add in SIM.
        iOwnWf SIM. clear - WF. apply GRA.padding_wf in WF. des. ss.
      }
      iDestruct SIM. subst.
      assert(x = ns0).
      { iMerge SIM PRE. rewrite <- own_sep in SIM. rewrite GRA.padding_add in SIM.
        iOwnWf SIM. eapply GRA.padding_wf in WF. des. eapply URA.auth_included in WF. des.
        clear - WF.
        Local Transparent URA.add.
        rr in WF. des. ss. des_ifs.
        Local Opaque URA.add.
      }
      subst.




      destruct (unint vret_src) eqn:T; cycle 1.
      { steps. unfold triggerUB. steps. }
      destruct vret_src; ss. clarify. steps.

      destruct (dec z (- 1)%Z).
      - subst. ss. steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ __ (A, SIM) (@URA.unit Σ) PRE; ss; et.
        { esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. }
        { esplits; ss; et. }
        { esplits; ss; et. exists ns0; iRefresh. left; iRefresh. iSplit SIM A; ss. r_solve. }
        steps.
        hret_tac mr (@URA.unit Σ); ss.
        { eapply URA.extends_updatable. esplit. r_equalize; r_solve. }
        { iRefresh. iDestruct SIM0. esplits; eauto. eexists; iRefresh. eauto. }
      - steps.
        force_l. eexists 1. steps. rewrite Any.upcast_downcast. ss. steps.

        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("push", [ll0; Vint z]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ (ord_pure 2) PRE SIM A; ss; et.
        { instantiate (1:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. iApply A; ss. }
        { esplits; ss; et. exists ns0; iRefresh. right; iRefresh; ss. }
        des; iRefresh. do 2 iDestruct POST0. iPure A. subst. apply Any.upcast_inj in A. des; clarify.
        iDestruct SIM0. destruct SIM0; iRefresh.
        { exfalso. iDestruct H1; subst. iMerge H1 SIM. rewrite <- own_sep in H1. rewrite GRA.padding_add in H1.
          iOwnWf H1. clear - WF. apply GRA.padding_wf in WF. des. ss.
        }


        rename H1 into A. iMerge A SIM. rewrite <- own_sep in A. rewrite GRA.padding_add in A. rewrite URA.add_comm in A.


        assert(x9 = ns0).
        { iOwnWf A. eapply GRA.padding_wf in WF. des. eapply URA.auth_included in WF. des.
          clear - WF.
          Local Transparent URA.add.
          rr in WF. des. ss. des_ifs.
          Local Opaque URA.add.
        }
        subst.

        Ltac iUpdate H :=
          eapply own_update in H;
          [let wf := fresh "WF" in let upd := fresh "UPD" in destruct H as [? [H [wf upd]]]; on_wf ltac:(fun H => clear H); rewrite gwf_mark_spec in wf; iRefresh| |
          on_wf ltac:(fun H => eapply wf_downward; [|exact H]); eexists ε; r_equalize; r_solve; fail]; cycle 1.
        iUpdate A.
        { eapply GRA.padding_updatable. instantiate (1:= echo_black (z :: ns0) ⋅ echo_white (z :: ns0)).
          eapply URA.auth_update. rr. ii. des; ss. destruct ctx; ss; clarify.
        }
        rewrite <- GRA.padding_add in A. rewrite own_sep in A. iDestruct A. subst.


        rewrite unfold_APC. steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast in *. steps.

        hcall_tac __ ord_top (POST0, A) (@URA.unit Σ) A0; ss; et.
        { esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. }
        { esplits; ss; eauto. exists (z :: ns0); iRefresh. left; iRefresh. iSplit A POST0; ss; r_solve. }
        steps.
        hret_tac mr0 (@URA.unit Σ); ss.
        { eapply URA.extends_updatable; et. r_equalize; r_solve. }
        { esplits; eauto. }
    }
    econs; ss.
    { admit "TODO". }
    (* { HoareDef.init. *)
    (*   unfold checkWf, forge, discard, put. steps. *)
    (*   unfold echo_finishF, echo_finish_body. steps. *)
    (*   iRefresh. do 2 iDestruct _ASSUME0. iPure A. iPure A0. clarify. *)
    (*   iDestruct SIM. *)
    (*   destruct SIM as [A|A]; iRefresh; cycle 1. *)
    (*   { exfalso. iMerge A _ASSUME0. rewrite <- own_sep in A. rewrite GRA.padding_add in A. *)
    (*     iOwnWf A. clear - WF. apply GRA.padding_wf in WF. des. ss. *)
    (*   } *)



    (*   iDestruct A. subst. *)
    (*   rename x into ns. rename x0 into ns0. *)
    (*   assert(ns = ns0). *)
    (*   { iMerge A _ASSUME0. rewrite <- own_sep in A. rewrite GRA.padding_add in A. *)
    (*     iOwnWf A. eapply GRA.padding_wf in WF. des. eapply URA.auth_included in WF. des. *)
    (*     clear - WF. *)
    (*     Local Transparent URA.add. *)
    (*     rr in WF. des. ss. des_ifs. *)
    (*     Local Opaque URA.add. *)
    (*   } *)
    (*   subst. *)




    (*   steps. unfold hcall, ccall. steps. *)
    (*   unfold body_to_tgt. unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************) *)

    (*   destruct ns0; ss. *)
    (*   - steps. rewrite Any.upcast_downcast. ss. steps. *)
    (*     rewrite unfold_is_list in A0. iPure A0. subst. ss. steps. *)
    (*     force_l. esplit. force_l. eexists (_, _). steps. force_l. { refl. } steps. force_l. esplit. force_l; ss. steps. *)
    (*     force_l. esplit. force_l. { refl. } steps. *)
    (*     { unfold alist_add. esplits; ss; eauto. eexists; iRefresh. left; iRefresh. instantiate (1:=[]). ss. iSplitL A; ss. } *)
    (*   - steps. rewrite Any.upcast_downcast. ss. steps. *)
    (*     force_l. eexists 3. steps. *)


    (*     assert(T: is_zero ll = false). *)
    (*     { rewrite unfold_is_list in *. do 4 iDestruct A0. iPure A0. subst. ss. } *)
    (*     rewrite T. clear T. *)
    (*     steps. *)


    (*     (* rr in A0. rr in A. rr in _ASSUME0. *) *)
    (*     (*** x2 x1 x5 ***) *)

    (*     rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("alloc", [Vint 1]↑). steps. *)
    (*     force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps. *)
    (*     unfold HoareCall at 3, checkWf, forge, discard, put. steps. force_l. eexists (x5, x2 ⋅ x1). steps. force_l. *)
    (*     { rewrite URA.unit_idl. eapply URA.extends_updatable. r_equalize; r_solve. } *)
    (*     steps. force_l. eexists ε. steps. force_l. eexists _. steps. force_l. { rewrite URA.unit_idl. refl. } steps. *)
    (*     force_l. eexists 1. steps. force_l. esplits. steps. force_l. esplits. steps. force_l. *)
    (*     { esplits; try refl. esplits; ss. } *)
    (*     steps. force_l. { esplits; ss; try lia. } steps. *)
    (*     clear_until _ASSUME0. *)
    (*     gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. *)
    (*     { unfold alist_add; ss. esplits; ss; eauto. exists (z :: ns0); iRefresh. right; iRefresh; ss. } *)
    (*     exists 400. des. clarify. unfold alist_add; cbn. steps. *)
    (*     des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'. *)

    (*     do 2 iDestruct _ASSUME2. iPure _ASSUME2. subst. apply Any.upcast_inj in _ASSUME2. des; clarify. *)
    (*     iDestruct SIM. destruct SIM as [B|B]; iRefresh. *)
    (*     { exfalso. iDestruct B; subst. iMerge B A. rewrite <- own_sep in B. rewrite GRA.padding_add in B. *)
    (*       iOwnWf B. clear - WF. apply GRA.padding_wf in WF. des. ss. *)
    (*     } *)
    (*     assert(x = z :: ns0). *)
    (*     { iMerge A B. rewrite <- own_sep in A. rewrite GRA.padding_add in A. *)
    (*       iOwnWf A. eapply GRA.padding_wf in WF. des. eapply URA.auth_included in WF. des. *)
    (*       clear - WF. *)
    (*       Local Transparent URA.add. *)
    (*       rr in WF. des. ss. des_ifs. *)
    (*       Local Opaque URA.add. *)
    (*     } *)
    (*     subst. *)
    (*     steps. *)










    (*     rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("pop2", [ll; Vptr x0 0]↑). steps. *)
    (*     force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps. *)
    (*     unfold HoareCall at 3, checkWf, forge, discard, put. steps. force_l. eexists (mr, x1 ⋅ x2 ⋅ x3 ⋅ x7). steps. force_l. *)
    (*     { eapply URA.extends_updatable. r_equalize; r_solve. } *)
    (*     steps. force_l. exists (x2 ⋅ x7). steps. force_l. eexists _. steps. force_l. *)
    (*     { symmetry. r_equalize; r_solve. } steps. *)
    (*     force_l. eexists (List.map Vint (z :: ns0), x0). steps. force_l. esplits. steps. force_l. esplits. steps. force_l. *)
    (*     { esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplit A0 A1; ss. *)
    (*       - iSplitP; ss. *)
    (*       - eexists; iRefresh. iApply A1; ss. } *)
    (*     steps. force_l. { esplits; ss; try lia. } steps. *)
    (*     clear_until A. *)
    (*     gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. *)
    (*     { unfold alist_add; ss. esplits; ss; eauto. exists (z :: ns0); iRefresh. right; iRefresh; ss. } *)
    (*     exists 400. des. clarify. unfold alist_add; cbn. steps. *)
    (*     des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'. *)
    (*     admit "TODO~~~~~~~~~~~~". *)
    (* } *)
  Unshelve.
    all: ss.
    all: try (by repeat econs; et).
  Qed.

End SIMMODSEM.


