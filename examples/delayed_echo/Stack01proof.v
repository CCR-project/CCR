Require Import Mem1 Mem2.
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



Section AUX.
  Context `{Σ: GRA.t}.

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
  Lemma _Own_ε: Own ε = ⌜True⌝. Proof. apply func_ext; i. unfold Own. apply prop_ext. split; i; ss. r. esplit. rewrite URA.unit_idl; refl. Qed.
  Lemma Own_ε: ⌞Own ε⌟. Proof. iIntro. rewrite _Own_ε. ss. Fail Qed. Abort. (********** coq bug !!!!!!!!!!!!!!! **************)
  Lemma Own_ε: ⌞Own ε⌟. Proof. iIntro. exists r. r_solve. Qed.
End AUX.
Global Opaque _APC.





Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).
  Eval compute in (@URA.car Mem1._memRA).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
        (<<SRC: mrps_src0 = Maps.add "Stack" (ε, tt↑) Maps.empty>>) /\
        (<<TGT: mrps_tgt0 = Maps.add "Stack" (ε, tt↑) Maps.empty>>)
  .

  Local Opaque points_to.

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.

  Lemma iHyp_update_r: forall P r0 r1, r0 = r1 -> iHyp P r0 -> iHyp P r1. Proof. i. subst. ss. Qed.

  Ltac iImpure H := let name := fresh "my_r" in
                    specialize (H ε URA.wf_unit I); rewrite intro_iHyp in H;
                    on_gwf ltac:(fun GWF => rewrite <- URA.unit_id in GWF; set (name:=ε) in GWF; eapply iHyp_update_r with (r1:=name) in H; [|refl]; clearbody name).



  Theorem correct: ModSemPair.sim Stack1.StackSem Stack0.StackSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. }

    econs; ss.
    { unfold popF. init.
      harg_tac. des_ifs_safe. des. repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *.
      iRefresh. do 4 iDestruct PRE. iMod A. iMod PRE. clarify.
      apply Any.upcast_inj in PRE. des; clarify. steps. rewrite Any.upcast_downcast in *. clarify. steps.

      unfold ccall, interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l. exists 7. steps.

      rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("load", [Vptr n 0]↑). steps.
      force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
      hcall_tac __ __ (@URA.unit Σ) A0 A1; ss; et.
      { instantiate (2:= (_, _, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss; et. }
      { esplits; ss; et. }
      des; subst. rewrite Any.upcast_downcast. steps. iRefresh. iDestruct POST. iMod A. apply Any.upcast_inj in A; des; clarify.


      destruct l; ss.
      - iMod A0. subst.
        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("cmp", [Vnullptr; Vnullptr]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ __ (@URA.unit Σ) POST (@URA.unit Σ); ss; et.
        { instantiate (2:= (_, _)). esplits; try refl; iRefresh. iSplitP; ss. hexploit Own_ε; intro A. iImpure A. iRefresh.
          TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT
          r.
          r in GWF. r in A.
          iSplitR A; ss; et. right. iRefresh. split; ss. }
        { esplits; ss; et. }
        des; subst. rewrite Any.upcast_downcast. steps. iRefresh. iDestruct POST. iMod A. apply Any.upcast_inj in A; des; clarify.



      des; subst. steps.



      unfold ccall.
      unfold body_to_tgt. unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.

      hcall_tac __ __ (A, A0) PRE (@URA.unit Σ); ss; et.
      { esplits; ss; et. eexists; iRefresh. left; iRefresh. iSplitL A; ss.
        - iApply A; ss.
        - iApply A0; ss.
      }
      des; subst. rewrite Any.upcast_downcast. steps. rewrite Any.upcast_downcast. steps.



      iDestruct SIM. destruct SIM as [SIM|SIM]; iRefresh; cycle 1.
      { hexploit echo_ra_white; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T PRE. iMod T; des; ss. }
      iDestruct SIM. subst.
      assert(ll0 = ll /\ x = ns); des; subst.
      { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T PRE. iMod T; des; ss. }
      subst.




      destruct (unint vret_src) eqn:T; cycle 1.
      { steps. unfold triggerUB. steps. }
      destruct vret_src; ss. clarify. steps.

      destruct (dec z (- 1)%Z).
      - subst. ss. steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ __ (A, SIM) (@URA.unit Σ) PRE; ss; et.
        { instantiate (2:= (_, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss; et. }
        { esplits; ss; et. }
        { esplits; ss; et. exists ns; iRefresh. left; iRefresh. iSplitL SIM; ss. }
        steps.
        hret_tac SIM0 (@URA.unit Σ); ss.
        { iRefresh. iDestruct SIM0. esplits; eauto. eexists; iRefresh. eauto. }
      - steps.
        force_l. eexists 1. steps. rewrite Any.upcast_downcast. ss. steps.

        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("push", [ll; Vint z]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        hcall_tac __ (ord_pure 2) PRE SIM A; ss; et.
        { instantiate (1:=(_, _)). esplits; try refl; iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. iApply A; ss. }
        { esplits; ss; et. exists ns; iRefresh. right; iRefresh; ss. }
        des; iRefresh. do 2 iDestruct POST0. iMod A. subst. apply Any.upcast_inj in A. des; clarify.
        iDestruct SIM0. destruct SIM0; iRefresh.
        { iDestruct H1. hexploit echo_ra_black; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T H1. iMod T; des; ss. }

        rename H1 into A.
        assert(ll0 = ll /\ x8 = ns); des; subst.
        { hexploit echo_ra_merge; et. intro T. iMod T. iSpecialize T SIM. iSpecialize T A. iMod T; des; ss. }




        iMerge A SIM. rewrite <- own_sep in A. rewrite GRA.embed_add in A. rewrite URA.add_comm in A.
        eapply own_upd in A; cycle 1; [|rewrite intro_iHyp in A;iMod A].
        { eapply GRA.embed_updatable. instantiate (1:= echo_black x (z :: ns) ⋅ echo_white x (z :: ns)).
          eapply URA.auth_update. rr. ii. des; ss. destruct ctx; ss; clarify.
        }
        rewrite <- GRA.embed_add in A. rewrite own_sep in A. iDestruct A. subst.



        rewrite unfold_APC. steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast in *. steps.

        hcall_tac __ ord_top (POST0, A) (@URA.unit Σ) A0; ss; et.
        { instantiate (1:=(_, _)). esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss; et. }
        { esplits; ss; eauto. exists (z :: ns); iRefresh. left; iRefresh. iSplitL A; ss. }
        steps.
        hret_tac SIM (@URA.unit Σ); ss.
        { esplits; eauto. }
    }
    { init.
      unfold checkWf, forge, discard, put. steps.
      unfold popF. steps.
      des. clarify.
      r in _ASSUME0. des. r in _ASSUME0. des; subst. r in _ASSUME1. des; subst. r in _ASSUME0. des; subst.

      iRefresh.
      iPure _ASSUME1. iPure _ASSUME2. subst.
      rewrite Any.upcast_downcast in *. clarify.
      apply Any.upcast_inj in _ASSUME1. des. clarify. clear EQ.
      steps. unfold ccall. steps.
      unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l. exists 7.
      steps. rewrite unfold_APC. steps. force_l. exists false. steps.
      force_l. eexists ("load", [Vptr n 0]↑). steps.
      force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
      unfold HoareCall, checkWf, forge, discard, put. steps.
      force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l.
      (* Ltac iHyply H := *)
      (*   match (type of H) with *)
      (*   | iHyp ?P ?r => apply r *)
      (*   end. *)
      iExists _ASSUME4. steps. force_l. eexists. steps. force_l.
      { instantiate (1:= a ⋅ b0 ⋅ b).
        (**************************************** we need some PCM solver, proof by reflection or something ******************************)
        (**************************************** we need some PCM solver, proof by reflection or something ******************************)
        (**************************************** we need some PCM solver, proof by reflection or something ******************************)
        admit "ez --- make PCM solver tactic".
      }
      steps.
      force_l. eexists (_, _, _). force_l. esplits. force_l. esplits. force_l.
      { split; [iRefresh|refl].
        Ltac iSplitP :=
          match goal with
          | |- ᐸ (Pure ?ph) ** ?pg ᐳ =>
            erewrite f_equal; cycle 1; [ instantiate (1 := (ε ⋅ _)); rewrite URA.unit_idl; refl | eapply sepconj_merge; iClears ]
          | |- ᐸ ?ph ** (Pure ?pg) ᐳ =>
            erewrite f_equal; cycle 1; [ instantiate (1 := (_ ⋅ ε)); rewrite URA.unit_id; refl | eapply sepconj_merge; iClears ]
          end
        .
        iSplitP; ss. iSplitP; ss. eauto.
      }
      steps; force_l. { esplits; ss; try lia. } steps.
      (***************************TODO: make call case ***********************)
      gstep; econs; try apply Nat.lt_succ_diag_r; i; ss.
      exists 400. des. clarify. clear_tac.
      steps. des. subst. rewrite Any.upcast_downcast in *. clarify. iRefresh.

      (* assert(WF: URA.wf x). *)
      (* { admit "FIX BUG IN HOARECALL". } *)
      (* replace (URA.extends (GRA.embed ((n, 0%Z) |-> [v])) x) with (((Own (GRA.embed ((n, 0%Z) |-> [v]))): iProp) x) in EXT by reflexivity. *)
      (* clear _ASSUME4. (***************** TODO: automatic clear when calling a function **************) *)
      steps.




      destruct l; ss.
      - (*********** cmp ***********)
        iPure _ASSUME3. clarify.
        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("cmp", [Vnullptr; Vnullptr]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iRefresh.
        exists ε. steps. force_l. esplits. force_l. { rewrite URA.unit_idl. refl. } steps.
        force_l. eexists (true, ε). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. iRefresh. iSplitP; ss.
          Set Nested Proofs Allowed.
          Lemma Own_ε: Own ε = ⌜True⌝. Proof. apply func_ext; i. unfold Own. apply prop_ext. split; i; ss. r. esplit. rewrite URA.unit_idl; refl. Qed.
          rewrite Own_ε. iSplitP; ss. right; iRefresh. rr. esplits; et. }
        force_l. { esplits; ss; try lia. }
        clear _GUARANTEE1 _GUARANTEE2 _GUARANTEE3 _GUARANTEE4.
        iDestruct _ASSUME1. iPure A. apply Any.upcast_inj in A. des; clarify.
        steps. gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iDestruct _ASSUME3. iPure A. subst. apply Any.upcast_inj in A. des; clarify.
       (*************************************************** iris presentaiton **********************************************)
       (*************************************************** iris presentaiton **********************************************)
       (*************************************************** iris presentaiton **********************************************)
       (*************************************************** iris presentaiton **********************************************)


        rewrite unfold_APC. steps. force_l. exists true. steps. force_l. esplits. force_l. esplits.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. esplits. steps. force_l.
        { esplits; et. rr. refl. }
        steps. force_l. esplit. steps. force_l. { refl. } steps.
      - repeat iDestruct _ASSUME3. iPure _ASSUME3. subst. iDestruct _ASSUME1. iPure A1. subst. apply Any.upcast_inj in A1. des; clarify.






        Ltac iDestruct' H :=
          match type of H with
          | iHyp (Exists _, _) _ => destruct H as [? H]; iRefresh
          | iHyp (_ ** _) _ =>
            let name0 := fresh "A" in
            apply sepconj_split in H as [? [? [H [name0 ?]]]]; subst; iRefresh
          end.
        Lemma Own_downward: forall r a0 a1, iHyp (Own r) a0 -> URA.extends a0 a1 -> iHyp (Own r) a1.
        Proof. i. eapply Own_extends; et. Qed.
        rewrite points_to_split in A0. rewrite <- GRA.embed_add in A0. rewrite own_sep in A0. ss.
        iDestruct' A0.





        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("cmp", [Vptr x0 0; Vnullptr]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        (* Ltac iExists' H := *)
        (*   match (type of H) with *)
        (*   | iHyp ?P ?r => first [exists r|apply r|fail] *)
        (*   end. *)
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists A0. steps. force_l. esplit.
        steps. force_l.
        { instantiate (1:=a ⋅ (x5 ⋅ (x7) ⋅ x4) ⋅ b ⋅ (x2 ⋅ x3)). admit "ez - pcm solver". } steps.
        force_l. eexists (false, _). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. iRefresh. iSplitP; ss.
          Ltac iSplitL Hs0 :=
            match goal with
            | |- ᐸ ?ph ** ?pg ᐳ =>
              let tmp := (r_gather Hs0) in
              erewrite f_equal; cycle 1; [instantiate (1 := _ ⋅ tmp)|eapply sepconj_merge; [(*** TODO: We don't use iClears here because there are unresolved existentials.
                                                             use pcm solver and put iClears ***)|iClears]]
            end.
          Ltac iSplitR Hs0 :=
            match goal with
            | |- ᐸ ?ph ** ?pg ᐳ =>
              let tmp := (r_gather Hs0) in
              erewrite f_equal; cycle 1; [instantiate (1 := _ ⋅ tmp)|eapply sepconj_merge; [(*** TODO: We don't use iClears here because there are unresolved existentials.
                                                             use pcm solver and put iClears ***)|iClears]]
            end.
          iSplitR A0.
          { (******** PCM SOLVER ********) rewrite URA.unit_idl; refl. }
          - do 4 left. do 3 eexists. iRefresh. iSplitP; ss. iSplitP; ss.
          - iApply A0; et. 
        }
        force_l. { esplits; ss; try lia. } clear _GUARANTEE2. des; ss. clear_tac. steps.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iDestruct _ASSUME3. iPure A2. apply Any.upcast_inj in A2. des; clarify.
        Ltac iClears' :=
          match goal with
          | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (([(_, (?src0, _))], ?src1), ?src2) (([(_, (?tgt0, _))], ?tgt1), ?tgt2)) ] =>
            let name := fresh "tmp" in
            let all := constr:(src0 ⋅ src1 ⋅ tgt0 ⋅ tgt1) in
            pose all as name;
            repeat multimatch goal with
                   | [H: iHyp ?ph ?rh |- _ ] =>
                     tryif r_contains rh all then idtac else clear H
                                                                   (* idtac H; *)
                                                                   (*   idtac rh; *)
                                                                   (*   tryif r_contains rh all then idtac "CONTAINS" else idtac "DROP" *)
                   end;
            clear name
          end.
        iClears'.
        (* iDestruct _GUARANTEE1. iPure A2. iDestruct _GUARANTEE1. iPure _GUARANTEE1. clear _GUARANTEE1 _GUARANTEE3. subst. *)




        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("load", [Vptr x0 0]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists _ASSUME3. steps. force_l. esplit.
        steps. force_l.
        { instantiate (1:=a ⋅ (x5 ⋅ x7 ⋅ x4) ⋅ b ⋅ (x2 ⋅ x3) ⋅ (x9)). admit "ez - pcm solver". } steps.
        force_l. eexists (x0, 0%Z, v0). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. iRefresh. iSplitP; ss. iSplitP; ss. }
        steps. force_l. { esplits; ss; try lia. } steps.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'. iDestruct _ASSUME5. iPure A0. apply Any.upcast_inj in A0. des; clarify.







        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("load", [Vptr x0 1]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists A1. steps. force_l. esplit.
        steps. force_l.
        { instantiate (1:=a ⋅ (x5 ⋅ x4) ⋅ b ⋅ (x2 ⋅ x3) ⋅ x9 ⋅ (x10 ⋅ x11)). admit "ez - pcm solver". } steps.
        force_l. eexists (x0, 1%Z, x1). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. iRefresh. iSplitP; ss. iSplitP; ss. }
        steps. force_l. { esplits; ss; try lia. } steps.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'. iDestruct _ASSUME6. iPure A0. apply Any.upcast_inj in A0. des; clarify.








        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("free", [Vptr x0 0]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists _ASSUME5. steps. force_l. esplit.
        steps. force_l.
        { instantiate (1:=a ⋅ (x5 ⋅ x4) ⋅ b ⋅ (x2 ⋅ x3) ⋅ x9 ⋅ (x11) ⋅ (x12 ⋅ x13)). admit "ez - pcm solver". } steps.
        force_l. eexists (x0, 0%Z). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. iApply _ASSUME5; ss. }
        steps. force_l. { esplits; ss; try lia. } steps.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.







        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("free", [Vptr x0 1]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists _ASSUME6. steps. force_l. esplit.
        steps. force_l.
        { instantiate (1:=a ⋅ (x5 ⋅ x4) ⋅ b ⋅ (x2 ⋅ x3) ⋅ x9 ⋅ x11 ⋅ (x13) ⋅ x6). admit "ez - pcm solver". } steps.
        force_l. eexists (x0, 1%Z). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. iApply _ASSUME6; ss. }
        steps. force_l. { esplits; ss; try lia. } steps.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.








        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("store", [Vptr n 0; x1]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists _ASSUME1. steps. force_l. esplit.
        steps. force_l.
        { instantiate (1:=a ⋅ (x5 ⋅ x4) ⋅ b ⋅ (x3) ⋅ x9 ⋅ x11 ⋅ x13 ⋅ x6 ⋅ x14). admit "ez - pcm solver". } steps.
        force_l. eexists (n, 0%Z, x1). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. iApply _ASSUME1; ss. }
        steps. force_l. { esplits; ss; try lia. } steps.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.





        Ltac iExists' Hs := let rs := r_gather Hs in exists rs.

        rewrite unfold_APC. steps. force_l. esplit. force_l. esplit. force_l. eexists (ε, _). steps.
        force_l. { refl. } steps. force_l. iExists' (A, _ASSUME10). force_l.
        { esplits; try refl. iRefresh. iSplitP; ss. eexists; iRefresh.
          iSplit _ASSUME10 A.
          { rewrite URA.add_comm. refl. (***************** TODO: pcm solver **********************) }
          iApply _ASSUME10; ss.
          iApply A; ss.
        }
        steps. force_l. esplit. force_l.
        { instantiate (1:=a ⋅ (x5) ⋅ b ⋅ x3 ⋅ x9 ⋅ x11 ⋅ x13 ⋅ x6 ⋅ x14). admit "ez - pcm solver". }
        steps.
    }
    econs; ss.
    { init.
      unfold checkWf, forge, discard, put. steps.
      unfold pop2F. steps.
      des. clarify.
      iRefresh. do 3 iDestruct _ASSUME0. iPure A. iDestruct A0. iDestruct _ASSUME0. iPure _ASSUME0.
      apply Any.upcast_inj in _ASSUME0. des; clarify.
      steps. rewrite Any.upcast_downcast in *. clarify.


      steps. unfold ccall. steps.
      unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      rename x2 into ll. rename l into xs.
      destruct xs; ss.
      - iPure A1. subst. force_l. exists 1. steps.



        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("cmp", [Vnullptr; Vnullptr]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. eexists ε. steps. force_l. esplit.
        steps. force_l.
        { refl. } steps.
        force_l. eexists (true, _). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. iRefresh. iSplitP; ss. rewrite Own_ε. iSplitP; ss. right. ss. }
        steps. force_l. { esplits; ss; try lia. } steps.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.
        iDestruct _ASSUME1. iPure A. apply Any.upcast_inj in A. des; clarify. steps.




        rewrite unfold_APC. steps. force_l. esplit. force_l. esplit.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. eexists ε. force_l.
        { esplits; try refl. }
        steps. force_l. esplit. force_l. { rewrite URA.unit_idl. refl. } steps.

      - do 4 iDestruct A1. iPure A1. subst. force_l. eexists 6. steps.
        rewrite points_to_split in A2. rewrite <- GRA.embed_add in A2. rewrite own_sep in A2. ss.
        iDestruct A2.



        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("cmp", [Vptr x 0; Vnullptr]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists A2. steps. force_l. esplit.
        steps. force_l.
        { instantiate (1:=(x8 ⋅ (x3 ⋅ (x9) ⋅ x2) ⋅ x6 ⋅ x4)). admit "ez - pcm solver". } steps.
        force_l. eexists (false, _). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. iRefresh. iSplitP; ss. iSplitR A2.
          { rewrite URA.unit_idl. refl. }
          - repeat left; iRefresh. do 3 eexists; iRefresh. iSplitP; ss. iSplitP; ss.
          - iApply A2; ss.
        }
        clear_until A0. steps. force_l. { esplits; ss; try lia. } steps.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.
        iDestruct _ASSUME1. iPure A2. apply Any.upcast_inj in A2. des; clarify.



        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("load", [Vptr x 0]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists _ASSUME1. steps. force_l. esplit.
        steps. force_l.
        { instantiate (1:=(x8 ⋅ (x3 ⋅ x9 ⋅ x2) ⋅ x6 ⋅ x4 ⋅ (x11))). admit "ez - pcm solver". } steps.
        force_l. eexists (x, 0%Z, v). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. iRefresh. iSplitP; ss. iSplitP; ss. }
        clear_until A0. steps. force_l. { esplits; ss; try lia. } steps.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.
        iDestruct _ASSUME3. iPure A2. apply Any.upcast_inj in A2. des; clarify.



        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("load", [Vptr x 1]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists A1. steps. force_l. esplit.
        steps. force_l.
        { instantiate (1:=x8 ⋅ (x3 ⋅ x2) ⋅ x6 ⋅ x4 ⋅ x11 ⋅ (x12 ⋅ x13)).
          (* Ltac r_check_equal := *)
          (*   match goal with *)
          (*   | [ |- ?rs0 = ?rs1 ] => *)
          (*     tryif (r_contains rs0 rs1; r_contains rs1 rs0) *)
          (*     then idtac *)
          (*     else fail 2 *)
          (*   end. *)
          (******* we need check_duplicate too. *********)
          admit "ez - pcm solver". } steps.
        force_l. eexists (x, 1%Z, x0). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl; iRefresh. iSplitP; ss. iSplitP; ss. }
        clear_until A0. steps. force_l. { esplits; ss; try lia. } steps.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.
        iDestruct _ASSUME4. iPure A1. apply Any.upcast_inj in A1. des; clarify.




        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("free", [Vptr x 0]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists _ASSUME3. steps. force_l. esplit.
        steps. force_l.
        { instantiate (1:=(x8 ⋅ (x3 ⋅ x2) ⋅ x6 ⋅ x4 ⋅ x11 ⋅ (x13) ⋅ (x14 ⋅ x15))). admit "ez - pcm solver". } steps.
        force_l. eexists (x, 0%Z). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. iApply _ASSUME3; ss. }
        clear_until A0. steps. force_l. { esplits; ss; try lia. } steps.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.




        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("free", [Vptr x 1]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists _ASSUME4. steps. force_l. esplit.
        steps. force_l.
        { instantiate (1:=(x8 ⋅ (x3 ⋅ x2) ⋅ x6 ⋅ x4 ⋅ x11 ⋅ x13 ⋅ (x15) ⋅ x5)). admit "ez - pcm solver". } steps.
        force_l. eexists (x, 1%Z). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. iApply _ASSUME4; ss. }
        clear_until A0. steps. force_l. { esplits; ss; try lia. } steps.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.




        rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("store", [Vptr n 0; v]↑). steps.
        force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
        unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
        force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists A0. steps. force_l. esplit.
        steps. force_l.
        { instantiate (1:=(x8 ⋅ (x3 ⋅ x2) ⋅ x4 ⋅ x11 ⋅ x13 ⋅ x15 ⋅ x5 ⋅ x16)). admit "ez - pcm solver". } steps.
        force_l. eexists (n, 0%Z, v). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
        { esplits; try refl. iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. iApply A0; ss. }
        clear_until A0. steps. force_l. { esplits; ss; try lia. } steps.
        gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
        des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.




        rewrite unfold_APC. steps. force_l. esplit. force_l. esplit. force_l. eexists (ε, _). steps.
        force_l. { refl. } steps. force_l. iExists' (A, _ASSUME8). force_l.
        { esplits; try refl. iRefresh. eexists; iRefresh. iSplit A _ASSUME8; ss. iSplitP; ss. }
        steps. force_l. esplit. force_l.
        { instantiate (1:=(x8 ⋅ (x3) ⋅ x4 ⋅ x11 ⋅ x13 ⋅ x15 ⋅ x5 ⋅ x16)). admit "ez - pcm solver". }
        steps.
    }
    econs; ss.
    { init.
      unfold checkWf, forge, discard, put. steps.
      unfold pushF. steps.
      des. clarify.
      iRefresh. do 3 iDestruct _ASSUME0. iPure A. iPure _ASSUME0.
      apply Any.upcast_inj in _ASSUME0. des; clarify.
      steps. rewrite Any.upcast_downcast in *. clarify.




      steps. unfold ccall. steps.
      unfold interp_hCallE_tgt, APC. steps. (********** TODO: never unfold it, make a lemma ******************)
      force_l. exists 3. steps.







      rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("alloc", [Vint 2]↑). steps.
      force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
      unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
      force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. eexists ε. steps. force_l. esplit.
      steps. force_l.
      { refl. } steps.
      force_l. eexists (2). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
      { esplits; try refl. iRefresh. ss. }
      steps. force_l. { esplits; ss; try lia. } steps.
      gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
      des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.
      do 2 iDestruct _ASSUME1. iPure _ASSUME1. apply Any.upcast_inj in _ASSUME1. des; clarify.
      rewrite points_to_split in A. rewrite <- GRA.embed_add in A. rewrite own_sep in A. ss. iDestruct A.





      rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("store", [Vptr x0 0; v]↑). steps.
      force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
      unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
      force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists A. steps. force_l. esplit.
      steps. force_l.
      { instantiate (1:=x5 ⋅ x6 ⋅ x4 ⋅ (x1 ⋅ (x7))). admit "ez - pcm solver". } steps.
      force_l. eexists (x0, 0%Z, v). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
      { esplits; try refl. iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. iApply A; ss. }
      steps. force_l. { esplits; ss; try lia. } steps.
      gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
      des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.






      rewrite unfold_APC. steps. force_l. exists false. steps. force_l. eexists ("store", [Vptr x0 1; x2]↑). steps.
      force_l; stb_tac; clarify. steps. rewrite Any.upcast_downcast. steps.
      unfold HoareCall, checkWf, forge, discard, put. steps. iRefresh.
      force_l. eexists (ε, _). steps. force_l. { refl. } steps. force_l. iExists A1. steps. force_l. esplit.
      steps. force_l.
      { instantiate (1:=x5 ⋅ x6 ⋅ x4 ⋅ (x1) ⋅ x3). admit "ez - pcm solver". } steps.
      force_l. eexists (x0, 1%Z, x2). esplits. steps. force_l. esplits. steps. force_l. esplits. steps. force_l.
      { esplits; try refl. iRefresh. eexists; iRefresh. iSplitP; ss. iSplitP; ss. iApply A1; ss. }
      steps. force_l. { esplits; ss; try lia. } steps.
      gstep; econs; try apply Nat.lt_succ_diag_r; i; ss. exists 400. des. clarify. unfold alist_add; cbn. steps.
      des. clarify. rewrite Any.upcast_downcast in *. clarify. iRefresh. iClears'.



      (********** v0 = ll' = x0, 0 = lhd 0 ***********)



      rewrite unfold_APC. steps. force_l. esplit. force_l. esplit. force_l. eexists (ε, _). steps.
      force_l. { refl. } steps. force_l. iExists' (A0, _ASSUME2, _ASSUME4). force_l.
      { esplits; try refl. iRefresh. eexists; iRefresh. iSplitP; ss. eexists; iRefresh. eexists; iRefresh.
        iSplit (_ASSUME2, _ASSUME4) A0.
        { admit "ez - pcm solver". }
        - iSplitP; ss. rewrite points_to_split. rewrite <- GRA.embed_add. rewrite own_sep. ss.
          iSplit _ASSUME2 _ASSUME4.
          { admit "ez - pcm solver". }
          + iApply _ASSUME2; ss.
          + iApply _ASSUME4; ss.
        - iApply A0; ss.
      }
      steps. force_l. esplit. force_l.
      { instantiate (1:=x5 ⋅ x4 ⋅ x1). admit "ez - pcm solver". }
      steps.
    }
  Unshelve.
    all: ss.
    all: try (by repeat econs; et).
  Qed.

End SIMMODSEM.


