Require Import LinkedList0 LinkedList1 SimModSem HoareDef.
Require Import Mem1.
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

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 tgt1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco3 (_sim_itree wf) _ _ _ n (([(_, src0)], src1), src2) (([(_, tgt0)], tgt1), tgt2))
      (at level 60,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' tgt1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").



Ltac prep := ired; try rewrite ! unfold_interp.

Ltac force_l :=
  prep;
  match goal with
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, guarantee ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [gstep; ired; eapply sim_itree_choose_src; [eauto|exists name]|contradict name]; cycle 1

  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_tgt; gstep; econs; eauto; unseal i_tgt
  end
.
Ltac force_r :=
  prep;
  match goal with
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    destruct (classic P) as [name|name]; [gstep; ired; eapply sim_itree_take_tgt; [eauto|exists name]|contradict name]; cycle 1

  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_src; gstep; econs; eauto; unseal i_src
  end
.
Ltac init :=
  split; ss; ii; clarify; rename y into varg; eexists 100%nat; ss; des; clarify;
  ginit; [eapply cpn3_wcompat; eauto with paco|]; unfold alist_add, alist_remove; ss;
  unfold fun_to_tgt, cfun, HoareFun; ss.

Ltac _step :=
  match goal with
  (*** blacklisting ***)
  (* | [ |- (gpaco3 (_sim_itree wf) _ _ _ _ (_, trigger (Choose _) >>= _) (_, ?i_tgt)) ] => idtac *)
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired; _step; ss; fail]
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    ired; gstep; eapply sim_itree_take_src; [apply Nat.lt_succ_diag_r|]; intro name

  (*** blacklisting ***)
  (* | [ |- (gpaco3 (_sim_itree wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired; _step; ss; fail]
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    ired; gstep; eapply sim_itree_choose_tgt; [apply Nat.lt_succ_diag_r|]; intro name



  | _ => (*** default ***)
    gstep; econs; try apply Nat.lt_succ_diag_r; i
  end;
  (* idtac *)
  match goal with
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end
.
Ltac steps := repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) unfold alist_add; simpl; des_ifs_safe).



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).
  Eval compute in (@URA.car Mem1._memRA).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
        (<<SRC: mrps_src0 = Maps.add "LinkedList" (ε, tt↑) Maps.empty>>) /\
        (<<TGT: mrps_tgt0 = Maps.add "LinkedList" (ε, tt↑) Maps.empty>>)
  .

  Local Opaque points_to.

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.










  (* Definition iApp (P: Σ -> Prop) (r: Σ): Prop := P r /\ URA.wf r. *)
  Definition iHyp (P: Σ -> Prop) (r: Σ): Prop := P r.
  (* Notation "'ᐸ ' P ' ᐳ'" := (iApp P _) (at level 60). (* (format "'ᐸ'  P  'ᐳ'") *) *)
  Notation "'ᐸ' P 'ᐳ'" := (iHyp P _) (at level 60). (* (format "'ᐸ'  P  'ᐳ'") *)
  Goal forall a, (iHyp  (fun _ => True) a). Abort.

  Lemma intro_iHyp: forall P r, P r = iHyp P r.
    { i. unfold iHyp. apply prop_ext. split; i; des; et. }
  Qed.

  Lemma wf_split: forall (a b: Σ), URA.wf (a ⋅ b) -> URA.wf a /\ URA.wf b.
    { i. split; eapply URA.wf_mon; et. rewrite URA.add_comm; et. }
  Qed.

  Ltac iSimplWf :=
    repeat match goal with
           | [H: URA.wf (?a ⋅ ?b) |- _ ] =>
             repeat (try rewrite URA.unit_id in H; try rewrite URA.unit_idl in H);
             apply wf_split in H; destruct H
           end.

  (* Definition iEnv: Type := list (iProp * Σ). *)
  (* Definition iEnvWf: iEnv -> Prop := fun ie => URA.wf (List.fold_left (⋅) (List.map snd ie) ε). *)

  Ltac on_first_hyp tac :=
    match reverse goal with [ H : _ |- _ ] => first [ tac H | fail 1 ] end.

  Definition IPROPS: Prop := forall x, x - x = 0.
  Lemma IPROPS_intro: IPROPS. r. i. rewrite Nat.sub_diag. ss. Qed.

  Ltac to_bar TAC :=
    match goal with
    | [H: IPROPS |- _ ] => TAC H
    | _ => idtac
    end.

  Ltac bar :=
    to_bar ltac:(fun _ => fail 1);
    let NAME := fresh "ㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡㅡ" in
    assert (NAME : IPROPS) by (exact IPROPS_intro)
  .

  Goal False.
    bar. clear_tac. Fail bar.
  Abort.

  Goal forall (a b c: Σ), False.
    i.
    Ltac r_length ls :=
      match ls with
      | (?x ⋅ ?y) =>
        let xl := r_length x in
        let yl := r_length y in
        constr:(xl + yl)
      | _ => constr:(1)
      end.
    let n := r_length (a ⋅ b ⋅ c) in pose n.

    Ltac r_in r rs :=
      match rs with
      | r => idtac
      | (r ⋅ ?y) => idtac
      | (?x ⋅ r) => idtac
      | (?x ⋅ ?y) => r_in r x + r_in r y
      | _ => fail
      end.
    (r_in a (a ⋅ b ⋅ c)).
    (r_in b (a ⋅ b ⋅ c)).
    (r_in c (a ⋅ b ⋅ c)).
    (r_in a (a ⋅ b)).
    (r_in b (a ⋅ b)).
    Fail (r_in c (a ⋅ b)).
    Fail (r_in a (b)).
    (r_in b (b)).
    Fail (r_in c (b)).

    Ltac r_contains xs ys :=
      match xs with
      | (?x0 ⋅ ?x1) => r_contains x0 ys; r_contains x1 ys
      | _ => r_in xs ys
      end.
    (r_contains a (a ⋅ b ⋅ c)).
    (r_contains b (a ⋅ b ⋅ c)).
    (r_contains c (a ⋅ b ⋅ c)).
    (r_contains a (a ⋅ b)).
    (r_contains b (a ⋅ b)).
    Fail (r_contains c (a ⋅ b)).
    Fail (r_contains a (b)).
    (r_contains b (b)).
    Fail (r_contains c (b)).

    (r_contains (a ⋅ b) (a ⋅ b ⋅ c)).
    (r_contains (b ⋅ a) (a ⋅ b ⋅ c)).
    (r_contains (b ⋅ c) (a ⋅ b ⋅ c)).
    (r_contains (c ⋅ a ⋅ b) (a ⋅ b ⋅ c)).
    Fail (r_contains (c ⋅ a ⋅ b) (a ⋅ b)).
    Fail (r_contains (a ⋅ c) (a ⋅ b)).
  Abort.

  Ltac iClears := match goal with
                  | [ |- iHyp _ ?rgoal ] =>
                    repeat multimatch goal with
                           | [ H: iHyp _ ?r |- _ ] =>
                             tryif r_contains r rgoal
                             then idtac
                             else clear H
                           end
                  end.

  Ltac iRefresh :=
    try bar;
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
         iClears)
  .

  Lemma sepconj_merge: forall (a b: Σ) (Pa Pb: iProp), iHyp Pa a -> iHyp Pb b -> iHyp (Pa ** Pb) (a ⋅ b).
  Proof. i. rr. esplits; eauto. Qed.

  Ltac pcm_solver := idtac.

  Ltac iMerge H0 G0 :=
    match goal with
    | [H: iHyp ?ph ?rh |- _ ] =>
      check_equal H H0;
      match goal with
      | [G: iHyp ?pg ?rg |- _ ] =>
        check_equal G G0;
        let name := fresh "tmp" in
        rename H into name;
        assert(H: iHyp (ph ** pg) (rh ⋅ rg)) by (apply sepconj_merge; try assumption);
        clear name; clear G
      end
    end
  .

  Ltac iApply H := erewrite f_equal; [apply H|pcm_solver].

  Goal forall (a b: Σ) (Pa Pb: iProp), Pa a -> Pb b -> URA.wf (a ⋅ b) -> (Pa ** Pb) (b ⋅ a).
    i. iRefresh.
    iMerge H0 H1.
    iApply H0.
    rewrite URA.add_comm. ss.
  Qed.

  Ltac idtacs Hs :=
    match Hs with
    | (?H0, ?H1) => idtacs H0; idtacs H1
    | ?H => idtac H
    end
  .

  Ltac r_gather Hs :=
    match Hs with
    | (?H0, ?H1) =>
      let rs0 := r_gather H0 in
      let rs1 := r_gather H1 in
      constr:(rs0 ⋅ rs1)
    | ?H =>
      match (type of H) with
      | iHyp _ ?rh => constr:(rh)
      end
        (* match goal with *)
        (* | [G: iHyp ?ph ?rh |- _ ] => *)
        (*   check_equal H G; *)
        (*   constr:(rh) *)
        (* end *)
    end.

  Ltac iSplit Hs0 Hs1 :=
    match goal with
    | [ |- iHyp (?ph ** ?pg) _ ] =>
      let tmp0 := (r_gather Hs0) in
      let tmp1 := (r_gather Hs1) in
      erewrite f_equal; cycle 1; [instantiate (1:= tmp0 ⋅ tmp1)|eapply sepconj_merge; iClears]
    end
  .

  Goal forall (a b c: Σ) (Pa Pb Pc: iProp), Pa a -> Pb b -> Pc c -> URA.wf (a ⋅ b ⋅ c) -> (Pa ** Pc ** Pb) (c ⋅ b ⋅ a).
    i. iRefresh.
    iSplit (H0, H2) H1.
    { admit "pcm solver". }
    admit "okay".
    admit "okay".
  Abort.

  Lemma sepconj_split: (forall (ab : Σ) (Pa Pb : iProp), iHyp (Pa ** Pb) (ab) -> exists a b, iHyp Pa a /\ iHyp Pb b /\ ab = a ⋅ b).
    { clear - Σ. ii. unfold iHyp in *. r in H. destruct H; clear H. des. esplits; et. }
  Qed.





  Theorem correct: ModSemPair.sim LinkedList1.LinkedListSem LinkedList0.LinkedListSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. }

    Opaque MemStb LinkedListStb.
    econs; ss.
    { init.
      unfold checkWf, forge, discard, put. steps.
      unfold popF. steps.
      des. clarify.
      r in _ASSUME0. des. r in _ASSUME0. des; subst. r in _ASSUME1. des; subst. r in _ASSUME0. des; subst.

      iRefresh.
      Ltac iPure H := rr in H; to_bar ltac:(fun BAR => move H after BAR). (* ; iRefresh. *)
      iPure _ASSUME1. iPure _ASSUME2. subst.
      rewrite Any.upcast_downcast in *. clarify.
      apply Any.upcast_inj in _ASSUME1. des. clarify. clear EQ.
      steps. unfold ccall. steps.
      unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l. exists 7.
      assert(unfold_APC: forall n, _APC n =
                         match n with
                         | 0 => Ret tt
                         | S n =>
                           break <- trigger (Choose _);;
                           if break: bool
                           then Ret tt
                           else
                             '(fn, varg) <- trigger (Choose _);;
                             trigger (hCall true fn varg);;
                             _APC n
                         end).
      { i. destruct n0; ss. }
      Opaque _APC.
      steps. rewrite unfold_APC. steps. force_l. exists false. steps.
      force_l. eexists ("load", [Vptr n 0]↑). steps.
      Transparent MemStb. cbn in Heq. Opaque MemStb.
      ss. clarify. rewrite Any.upcast_downcast. steps.
      unfold HoareCall, checkWf, forge, discard, put. steps.
      force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l.
      (* Ltac iHyply H := *)
      (*   match (type of H) with *)
      (*   | iHyp ?P ?r => apply r *)
      (*   end. *)
      Ltac iExists H :=
        match (type of H) with
        | iHyp ?P ?r => exists r
        end.
      iExists _ASSUME4. steps. force_l. eexists. steps. force_l.
      { instantiate (1:= a ⋅ b0 ⋅ b).
        (**************************************** we need some PCM solver, proof by reflection or something ******************************)
        (**************************************** we need some PCM solver, proof by reflection or something ******************************)
        (**************************************** we need some PCM solver, proof by reflection or something ******************************)
        admit "ez --- make PCM solver tactic".
      }
      steps.
      force_l. eexists (_, _, _). force_l. esplits. force_l. esplits. force_l.
      { esplits; eauto. instantiate (1:= x2).
        admit "change equality to extends; or we can choose precise one".
      }
      force_l.
      { esplits; ss; try lia. }
      des. clear _GUARANTEE6. clarify. clear_tac.
      (***************************TODO: make call case ***********************)
      gstep; econs; try apply Nat.lt_succ_diag_r; i; ss.
      exists 400. des. clarify. clear_tac.
      steps. des.
      assert(EXT: URA.extends (GRA.padding ((n, 0%Z) |-> [x2])) x).
      { subst; refl. }
      clear _ASSUME0.
      clarify. apply Any.upcast_inj in _ASSUME2. des; clarify. rewrite Any.upcast_downcast in *. clarify. clear_tac.

      Ltac clear_bar := to_bar ltac:(fun H => clear H).
      clear_bar; iRefresh.

      (* assert(WF: URA.wf x). *)
      (* { admit "FIX BUG IN HOARECALL". } *)
      (* replace (URA.extends (GRA.padding ((n, 0%Z) |-> [v])) x) with (((Own (GRA.padding ((n, 0%Z) |-> [v]))): iProp) x) in EXT by reflexivity. *)
      (* clear _ASSUME4. (***************** TODO: automatic clear when calling a function **************) *)
      steps.




      destruct l; ss.
      - (*********** cmp ***********)
        iPure _ASSUME3. clarify.
        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("cmp", [Vnullptr; Vnullptr]↑). steps.
        Transparent MemStb. cbn in Heq. Opaque MemStb. ss. clarify. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. clear_bar; iRefresh.
        exists ε. steps. force_l. esplits. force_l. { rewrite URA.unit_idl. refl. } steps.
        force_l. eexists (true, _). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. repeat right. esplits; et. }
        force_l.
        { esplits; ss; try lia. }
        clear _GUARANTEE2.
        des; ss. clear_tac.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. apply Any.upcast_inj in _ASSUME2. des; clarify.


        rewrite unfold_APC. steps. force_l. exists true. steps. force_l. esplits. force_l. esplits.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. esplits. steps. force_l.
        { esplits; et. rr. refl. }
        steps. force_l. esplit. steps. force_l. { refl. } steps.
      - Ltac iDestruct H :=
          match type of H with
          | iHyp (Exists _, _) _ => destruct H as [? H]; clear_bar; iRefresh
          | iHyp (_ ** _) _ =>
            let name0 := fresh "A" in
            apply sepconj_split in H as [? [? [H [name0 ?]]]]; clear_bar; iRefresh
            (* apply sepconj_split in H as [? [? ?]]; clear_bar; iRefresh *)
          end.
        repeat iDestruct _ASSUME3. iPure _ASSUME3. subst.



        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("cmp", [Vptr x 0; Vnullptr]↑). steps.
        Transparent MemStb. cbn in Heq. Opaque MemStb. ss. clarify. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        Ltac iExists' H :=
          match (type of H) with
          | iHyp ?P ?r => first [exists r|apply r|fail]
          end.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists A0. steps. force_l. esplit.
        steps. force_l.
        { instantiate (1:= a ⋅ (x3 ⋅ x2) ⋅ b ⋅ GRA.padding ((n, 0%Z) |-> [Vptr x 0])). admit "ez - pcm solver". } steps.
        force_l. eexists (false, _). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. left. esplits; eauto. rr in A0. admit "ez - use extends instead of equality". }
        force_l. { esplits; ss; try lia. } clear _GUARANTEE2. des; ss. clear_tac.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. apply Any.upcast_inj in _ASSUME2. des; clarify.


        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("load", [Vptr x 0]↑). steps.
        Transparent MemStb. cbn in Heq. Opaque MemStb. ss. clarify. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists A0. steps. force_l. esplit.
        steps. force_l.
        { rewrite URA.add_comm with (a0:=x4). refl. } steps.
        force_l. eexists (x, 0%Z, Vint (Z.of_nat n0)). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. rr in A0. admit "ez - use extends instead of equality". }
        force_l. { esplits; ss; try lia. } clear _GUARANTEE2 _GUARANTEE3 _GUARANTEE4. clear_tac.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. apply Any.upcast_inj in _ASSUME3. des; clarify.


        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("load", [Vptr x 1]↑). steps.
        Transparent MemStb. cbn in Heq. Opaque MemStb. ss. clarify. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists A0. steps. force_l. esplit.
        steps. force_l.
        TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT
        { rewrite URA.add_comm with (a0:=x4). refl. } steps.
        force_l. eexists (x, 0%Z, Vint (Z.of_nat n0)). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. rr in A0. admit "ez - use extends instead of equality". }
        force_l. { esplits; ss; try lia. } clear _GUARANTEE2 _GUARANTEE3 _GUARANTEE4. clear_tac.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. apply Any.upcast_inj in _ASSUME3. des; clarify.








        apply sepconj_split in _ASSUME3; clear_bar; iRefresh.
        iDestruct _ASSUME3.
        apply sepconj_split in _ASSUME3. des.

        iDestruct _ASSUME3. iDestruct _ASSUME3.
        iDestruct _ASSUME3.
        rr in _ASSUME3. des.
        iDestruct _ASSUME3. rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("cmp", [Vnullptr; Vnullptr]↑). steps.
        Transparent MemStb. cbn in Heq. Opaque MemStb. ss. clarify. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. clear_bar; iRefresh.
        exists ε. steps. force_l. esplits. force_l. { rewrite URA.unit_idl. refl. } steps.
        force_l. eexists (true, _). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. repeat right. esplits; et. }
        force_l.
        { esplits; ss; try lia. }
        clear _GUARANTEE2.
        des; ss. clear_tac.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. apply Any.upcast_inj in _ASSUME2. des; clarify.








        Transparent MemStb. cbn in Heq. Opaque MemStb. ss. clarify. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. clear_bar; iRefresh.
        exists ε. steps. force_l. esplits. force_l. { rewrite URA.unit_idl. refl. } steps.
        force_l. eexists (true, _). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. repeat right. esplits; et. }
        force_l.
        { esplits; ss; try lia. }
        clear _GUARANTEE3 _GUARANTEE4.
        steps.
        des; ss. clear_tac.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.


        TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT

        iRefresh. clear _GUARANTEE6. clarify. clear_tac.
        (***************************TODO: make call case ***********************)
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss.
        exists 400. des. clarify. clear_tac.
        steps. des.
        assert(EXT: URA.extends (GRA.padding ((n, 0%Z) |-> [x2])) x).
        { subst; refl. }
        clear _ASSUME0.
        clarify. apply Any.upcast_inj in _ASSUME1. des; clarify. rewrite Any.upcast_downcast in *. clarify.

        assert(WF: URA.wf x).
        { admit "FIX BUG IN HOARECALL". }
        replace (URA.extends (GRA.padding ((n, 0%Z) |-> [v])) x) with (((Own (GRA.padding ((n, 0%Z) |-> [v]))): iProp) x) in EXT by reflexivity.
        clear _ASSUME4. (***************** TODO: automatic clear when calling a function **************)
        steps.
      -
      }
      force_l.
      { esplits; ss; try lia. }
      des. clear _GUARANTEE6. clarify. clear_tac.
      (***************************TODO: make call case ***********************)
      gstep; econs; try apply Nat.lt_succ_diag_r; i; ss.
      exists 400. des. clarify. clear_tac.
      steps. des.
      assert(EXT: URA.extends (GRA.padding ((n, 0%Z) |-> [x2])) x).
      { subst; refl. }
      clear _ASSUME0.
      clarify. apply Any.upcast_inj in _ASSUME1. des; clarify. rewrite Any.upcast_downcast in *. clarify.

      assert(WF: URA.wf x).
      { admit "FIX BUG IN HOARECALL". }
      replace (URA.extends (GRA.padding ((n, 0%Z) |-> [v])) x) with (((Own (GRA.padding ((n, 0%Z) |-> [v]))): iProp) x) in EXT by reflexivity.
      clear _ASSUME4. (***************** TODO: automatic clear when calling a function **************)
      steps.











      (********************************************************************************************)
      TTTTTTTTTTTTt
      iRefresh.
      steps.
      { unfold alist_find.
      _step.
      (prep; try _step; unfold alist_add; simpl; des_ifs_safe).
      steps.
      idtac.
      unshelve eexists.
      {
        iHyply _ASSUME4.
      }
          eapply b1.
      eexists. steps. force_l. eexists.
      force_l.
      { apply _ASSUME4.
      }
      idtac.
      {
      unshelve eexists.
      {
      instantiate (1:=).  repeat rewrite URA.unit_id. refl. }
      steps.

      iRefresh.
      des. clarify. rewrite Any.upcast_downcast in *. clarify. apply_all_once Any.upcast_inj. des. clarify. clear_tac.
      steps.
      unfold APC. unfold interp_hCallE_tgt. steps. force_l. exists 0. steps. force_l. esplits; eauto.
      force_l. esplits; eauto. force_l.
      set (blk := (Mem.nb mem_tgt)) in *.
      rename x0 into sz. rename _ASSUME into WF.
      set (mem_src_new := add_delta_to_black
                            (URA.black (mem_src: URA.car (t:=Mem1._memRA)))
                            (points_to (blk, 0%Z) (repeat (Vint 0) sz))).
      eexists (GRA.padding (mem_src_new: URA.car (t:=Mem1.memRA)),
               GRA.padding ((blk, 0%Z) |-> (repeat (Vint 0) sz))).
      Local Opaque URA.add. steps.
      assert(WFA: forall ofs, mem_src (Mem.nb mem_tgt) ofs = inr tt).
      { i.
        destruct (mem_src (Mem.nb mem_tgt) ofs) eqn:A; cycle 1.
        { des_u; ss. }
        destruct o.
        - admit "ez - add tgt wf".
        - admit "ez - inl None is boom in RA.excl".
      }
      rewrite URA.unit_idl in *. rewrite ! GRA.padding_add.
      force_l.
      { etrans.
        { eapply URA.extends_updatable. eexists; et. }
        eapply GRA.padding_updatable.
        ss.
        replace (URA.excl ((mem_src: URA.car (t:=Mem1._memRA)) ⋅ f) ε) with
            (URA.black ((mem_src: URA.car (t:=Mem1._memRA)) ⋅ f)) by ss.
        eapply URA.auth_alloc2.
        eapply URA.wf_mon in WF.
        eapply GRA.padding_wf in WF. des.
        clear - WF WFA Heq NULLPTR SIM.
        Local Transparent URA.add points_to.
        ss. des. unfold URA.white in Heq. clarify.
        ii. des_ifs; ss.
        - bsimpl; des; des_sumbool; clarify.
          exploit WFA; et. intro A. rewrite A in *; ss.
        - specialize (WF0 k k0). bsimpl; des; des_sumbool; clarify; des_ifs.
        - specialize (WF0 k k0). bsimpl; des; des_sumbool; clarify; des_ifs.
          apply_all_once Z.leb_le. apply_all_once Z.ltb_lt.
          intro A. apply nth_error_None in A. rewrite repeat_length in *.
          apply inj_le in A. rewrite Z2Nat.id in A; cycle 1.
          { lia. }
          lia.
        Local Opaque URA.add points_to.
      }
      Local Opaque URA.wf.
      ss.
      steps. force_l. esplits; eauto. force_l.
      { esplits; eauto. }
      steps.
      force_l. esplits; eauto.
      force_l.
      { instantiate (1:= GRA.padding _). rewrite GRA.padding_add. rewrite URA.unit_id. f_equal. ss. }
      clear _GUARANTEE0 _GUARANTEE1.
      Local Opaque URA.add points_to.
      Local Transparent points_to.
      unfold points_to, URA.white in Heq. clarify. ss.
      eapply URA.wf_mon in WF. eapply GRA.padding_wf in WF. des. ss. des. clear_tac. clear WF.
      clear mem_src_new.
      steps. esplits; ss; cycle 1.
      - Local Transparent URA.add.
        ss. des_ifs. bsimpl; des; des_sumbool; ss.
        subst blk. clear - Heq1.
        admit "ez: add tgt wf".
        Local Opaque URA.add.
      - ss. ii.
        destruct (dec b blk).
        + subst. unfold blk. unfold update. des_ifs_safe.
          des_ifs.
          * bsimpl; des; try rewrite Z.leb_le in *; try rewrite Z.ltb_lt in *.
            Local Transparent URA.add.
            s.
            Local Opaque URA.add.
            des_ifs; bsimpl; des; des_sumbool; ss; clarify; try rewrite Z.leb_le in *; try rewrite Z.ltb_lt in *;
              try rewrite Z.leb_gt in *; try rewrite Z.ltb_ge in *; try lia; et.
            { exploit WFA; et. intro A. rewrite A in *; ss. }
            { exploit WFA; et. intro A. rewrite A in *; ss. }
            { rewrite Z.sub_0_r.
              destruct (nth_error (repeat (Vint 0) sz) (Z.to_nat ofs)) eqn:U.
              - eapply nth_error_In in U. eapply repeat_spec in U. subst. econs; et.
              - eapply nth_error_None in U. lia.
            }
            { rewrite repeat_length in *. lia. }
          * Local Transparent URA.add.
            s.
            Local Opaque URA.add.
            des_ifs; bsimpl; des; des_sumbool; ss; clarify; try rewrite Z.leb_le in *; try rewrite Z.ltb_lt in *;
              try rewrite Z.leb_gt in *; try rewrite Z.ltb_ge in *; try lia; et;
                try (by exploit WFA; et; intro A; rewrite A in *; ss).
            { rewrite Z.sub_0_r. rewrite repeat_length in *. lia. }
            { econs; eauto. }
            { econs; eauto. }
        + Local Transparent URA.add.
          ss.
          hexploit (SIM b ofs); et. intro A. inv A.
          {
            des_ifs; bsimpl; des; des_sumbool; clarify.
            - unfold update. des_ifs. rewrite <- H1. econs.
            - unfold update. des_ifs. rewrite <- H1. econs.
            - unfold update. des_ifs. rewrite <- H1. econs.
          }
          {
            des_ifs; bsimpl; des; des_sumbool; clarify.
            - unfold update. des_ifs. rewrite <- H1. econs.
            - unfold update. des_ifs. rewrite <- H1. econs.
            - unfold update. des_ifs. rewrite <- H1. econs.
          }
    }
    econs; ss.
    { init.
      Local Opaque URA.add URA.wf.
      unfold checkWf, forge, discard, put. steps.
      unfold freeF. steps. rewrite Any.upcast_downcast. steps.
      (************** TODO: rename x3 into ASSUME *********************)
      des. clarify. clear_tac. rewrite Any.upcast_downcast in *. clarify.
      clear v x5. (************ TODO: WHY? *******************)
      steps.
      unfold interp_hCallE_tgt. steps. force_l. exists 0. steps.
      apply_all_once Any.upcast_inj. des; clarify. clear_tac.
      rewrite URA.unit_idl in *. rewrite GRA.padding_add in *. eapply GRA.padding_wf in x1. des.
      rename x1 into WF.
      rename n into b. rename z into ofs. rename v0 into v.

      assert(A: mem_src b ofs = inl (Some v)).
      { Local Transparent URA.wf.
        ss. des_ifs. des. specialize (WF0 b ofs).
        Local Transparent URA.add.
        clear SIM.
        Local Transparent URA.unit.
        ss. clarify. rr in WF. des. clarify. ss.
        des_ifs;
          bsimpl; des; des_sumbool; ss;
          repeat des_u;
          clear_tac;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
          try rewrite Z.sub_diag in *;
          try lia; ss.
        Local Opaque URA.wf URA.add URA.unit.
      }

      set (mem_src' := fun _b _ofs => if dec _b b && dec _ofs ofs then inr () else mem_src _b _ofs).

      assert(WF': URA.wf (mem_src': URA.car (t:=Mem1._memRA))).
      { Local Transparent URA.add URA.wf.
        ss. ii. des_ifs.
        ss. clarify.
        subst mem_src'. ss. des_ifs. des. specialize (WF0 k k0). bsimpl. des; des_sumbool; des_ifs.
        Local Opaque URA.wf URA.add.
      }
      hexploit (SIM b ofs); et. intro B. rewrite A in *. inv B.
      force_r.
      { exfalso. unfold Mem.free in *. des_ifs. }
      rename t into mem_tgt'.
      assert(SIM': forall b ofs, sim_loc (Mem.cnts mem_tgt' b ofs) (mem_src' b ofs)).
      { i.
        unfold Mem.free in _UNWRAPU. des_ifs. ss.
        subst mem_src'. ss.
        destruct (classic (b = b0 /\ ofs = ofs0)); des; clarify.
        - destruct H0; clarify. (**** TODO: FIX ****) unfold update. des_ifs. econs.
        - des_ifs.
          { Psimpl. bsimpl; des; des_sumbool; ss; clarify. destruct H0; ss. destruct H1; ss. (**** TODO: FIX ****)}
          replace (update (Mem.cnts mem_tgt) b (update (Mem.cnts mem_tgt b) ofs None) b0 ofs0) with
              (Mem.cnts mem_tgt b0 ofs0); cycle 1.
          { unfold update. des_ifs. Psimpl. des_ifs; bsimpl; des; des_sumbool; ss; clarify. }
          et.
      }
      force_l. esplits.
      force_l. esplits. force_l.
      eexists ((GRA.padding (URA.black (mem_src': URA.car (t:=Mem1._memRA)))), URA.unit: URA.car (t:=Σ)).
      steps.
      steps. force_l.
      { rewrite URA.unit_id.
        rewrite ! GRA.padding_add. apply GRA.padding_updatable.
        apply URA.auth_dealloc.
        clear - WF' WF.
        r. i. rewrite URA.unit_idl.
        ss. destruct H; clear H. (*** coq bug; des infloops ***) des. clarify.
        esplits; et.
        apply func_ext. intro _b. apply func_ext. intro _ofs.
        destruct (classic (b = _b /\ ofs = _ofs)).
        - destruct H; clear H. clarify.
          subst mem_src'. ss. des_ifs; bsimpl; des; des_sumbool; clarify.
          clear - H0.
          Local Transparent URA.wf.
          Local Transparent URA.add.
          specialize (H0 _b _ofs). ss.
          des_ifs; bsimpl; des; des_sumbool;
            try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
              try rewrite Z.sub_diag in *;
              try lia; ss.
          des_u. ss.
        - Psimpl.
          subst mem_src'. s.
          des_ifs; bsimpl; des; des_sumbool;
            try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
              try rewrite Z.sub_diag in *;
              try lia; ss.
          Local Opaque URA.wf.
          Local Opaque URA.add.
      }
      steps. force_l. esplits. force_l. { esplits; eauto. } steps. force_l. esplits. force_l.
      { rewrite URA.unit_idl. ss. }
      steps.
      esplits; eauto.
      admit "ez - add a condition in wf, so that points-to predicate containing Vnullptr is never published".
    }
    Local Opaque points_to URA.add URA.wf URA.unit.
    econs.
    { init.
      unfold checkWf, forge, discard, put. steps.
      unfold loadF. steps. rewrite Any.upcast_downcast. steps.
      (************** TODO: rename x3 into ASSUME *********************)
      des. clarify. clear_tac. rewrite Any.upcast_downcast in *. clarify.
      apply_all_once Any.upcast_inj. des. clarify. clear_tac.
      rewrite URA.unit_idl in *. rewrite GRA.padding_add in *. apply_all_once GRA.padding_wf. des.
      ss.
      unfold interp_hCallE_tgt. steps. force_l. exists 0. steps. force_l. esplit. force_l. esplit.
      rename n into b. rename z into ofs.
      force_l. eexists (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA))),
                        GRA.padding ((b, ofs) |-> [v])).
      steps.
      force_l. { refl. } steps. force_l. esplit. force_l. { esplits; eauto. } steps.
      force_l. esplit. steps. force_l. { rewrite URA.unit_id. refl. } steps.
      assert(T: mem_src b ofs = inl (Some v)).
      { Local Transparent points_to URA.add URA.wf URA.unit.
        clear - x1.
        ss. des. do 2 spc x0. rr in x1. des. ss.
        des_ifs; bsimpl; des; des_sumbool; ss;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
            try rewrite Z.sub_diag in *; try lia; ss.
        Local Opaque points_to URA.add URA.wf URA.unit.
      }
      exploit SIM; et. intro U. rewrite T in U. inv U; ss. unfold Mem.load. force_r; ss. clarify. steps.
      esplits; eauto.
    }
    econs.
    { init.
      unfold checkWf, forge, discard, put. steps.
      unfold storeF. steps. rewrite Any.upcast_downcast. steps.
      (************** TODO: rename x3 into ASSUME *********************)
      des. clarify. clear_tac. rewrite Any.upcast_downcast in *. clarify.
      apply_all_once Any.upcast_inj. des. clarify. clear_tac.
      rewrite URA.unit_idl in *. rewrite GRA.padding_add in *. apply_all_once GRA.padding_wf. des.
      ss.
      unfold interp_hCallE_tgt. steps. force_l. exists 0. steps. force_l. esplit. force_l. esplit.
      rename n into b. rename z into ofs.
      set (mem_src' := fun _b _ofs => if dec _b b && dec _ofs ofs then inl (Some v) else mem_src _b _ofs).
      force_l. eexists (GRA.padding (URA.black (mem_src': URA.car (t:=Mem1._memRA))),
                        GRA.padding ((b, ofs) |-> [v])).
      rename x1 into WF.
      assert(WF0: URA.wf (mem_src': URA.car (t:=Mem1._memRA))).
      { Local Transparent URA.wf.
        clear - WF. apply URA.wf_mon in WF. ss. des.
        ii. specialize (WF0 k k0). des_ifs_safe. unfold mem_src' in *. des_ifs.
        Local Opaque URA.wf.
      }
      steps.
      force_l.
      { rewrite ! GRA.padding_add. eapply GRA.padding_updatable.
        clear - WF WF0. clear WF.
        Local Transparent URA.add GRA.to_URA points_to URA.wf URA.unit.
        eapply URA.auth_update; et.
        rr. ii. destruct H; clear H. (*** FIXME: des runs infloop ***)
        des. subst. esplits; et.
        subst mem_src'. do 2 (apply func_ext; i). specialize (H0 x x0). specialize (WF0 x x0). ss.
        des_ifs; bsimpl; des; des_sumbool; ss; subst;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
            try rewrite Z.sub_diag in *; try lia; ss.
        Local Opaque URA.add GRA.to_URA points_to URA.wf URA.unit.
      }
      steps. force_l. esplit. force_l. { esplits; eauto. } steps.
      force_l. esplit. steps. force_l. { rewrite URA.unit_id. refl. } steps.
      assert(v_old0 = v_old).
      { admit "TODO----------FIXTHIS". }
      subst.
      assert(U: mem_src b ofs = inl (Some v_old)).
      { Local Transparent URA.add GRA.to_URA points_to URA.wf URA.unit.
        clear - WF. ss. des. specialize (WF0 b ofs). r in WF. des; clarify. ss.
        des_ifs; bsimpl; des; des_sumbool; ss; subst;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
            try rewrite Z.sub_diag in *; try lia; ss.
        Local Opaque URA.add GRA.to_URA points_to URA.wf URA.unit.
      }
      hexploit SIM; et. intro V. rewrite U in V. inv V; ss. unfold Mem.store. rewrite <- H1. steps.
      esplits; eauto.
      { esplits; ss; et. des_ifs.
        - bsimpl; des; des_sumbool; ss; subst. unfold mem_src'. des_ifs; bsimpl; des; des_sumbool; ss. econs; et.
        - unfold mem_src'. des_ifs. bsimpl; des; des_sumbool; subst; ss.
      }
      admit "ez - add a condition in wf, so that points-to predicate containing Vnullptr is never published".
    }
    econs; et.
    { admit "MINKI!!!". }
  Unshelve.
    all: ss.
    all: try (by repeat econs; et).
  Qed.

End SIMMODSEM.


