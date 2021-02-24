Require Import Mem0 Mem1 SimModSem HoareDef.
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



(*** black + delta --> new_black ***)
Definition add_delta_to_black `{M: URA.t} (b: URA.auth_t) (w: URA.auth_t): URA.auth_t :=
  match b, w with
  | URA.excl e _, URA.frag f1 => URA.excl (URA.add e f1) URA.unit
  | _, _ => URA.boom
  end
.


(* Notation "wf n *)
(* '------------------------------------------------------------------' *)
(* src0 tgt0 *)
(* '------------------------------------------------------------------' *)
(* src1 tgt1 *)
(* '------------------------------------------------------------------' *)
(* src2 tgt2" := *)
(*   (sim_itree wf n (([(_, src0)], src1), src2) (([(_, tgt0)], tgt1), tgt2)) *)
(*     (at level 60, *)
(*      format "wf  n '//' *)
(* '------------------------------------------------------------------' '//' *)
(* src0 '//' *)
(* tgt0 '//' *)
(* '------------------------------------------------------------------' '//' *)
(* src1 '//' *)
(* tgt1 '//' *)
(* '------------------------------------------------------------------' '//' *)
(* src2 '//' '//' '//' *)
(* tgt2 '//' *)
(* "). *)
(******** TODO: it works in emacs but fails in coqc -- try coq 8.13 and uncomment it ***********)

Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 tgt1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco3 (_sim_itree wf) _ _ _ n (([(_, src0)], src1), src2) (([(_, tgt0)], tgt1), tgt2))
      (at level 60,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' tgt1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").



(* TODO: copied from Linkedlist01proof *)
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
  Context `{@GRA.inG Mem1.memRA Σ} `{@GRA.inG (RA.excl Mem.t) Σ}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).
  (* Eval compute in (@RA.car (RA.excl Mem.t)). *)
  Eval compute in (@URA.car Mem1._memRA).
  Inductive sim_loc: option val -> (option val + unit) -> Prop :=
  | sim_loc_present v: sim_loc (Some v) (inl (Some v))
  | sim_loc_absent: sim_loc None (inr tt)
  .

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists mem_src (mem_tgt: Mem.t),
        (<<SRC: mrps_src0 = Maps.add "Mem" ((GRA.padding ((URA.black mem_src): URA.car (t:=Mem1.memRA))), tt↑) Maps.empty>>) /\
        (<<TGT: mrps_tgt0 = Maps.add "Mem" (ε, mem_tgt↑) Maps.empty>>) /\
        (<<SIM: forall b ofs, sim_loc ((mem_tgt.(Mem.cnts)) b ofs) (mem_src b ofs)>>)
  .

  Local Opaque points_to.

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.

  Theorem correct: ModSemPair.sim Mem1.MemSem Mem0.MemSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. esplits; ss; et. ii.
      destruct (classic (b = 0%nat /\ ofs = 0%Z)).
      - des. subst. ss. unfold update. des_ifs. econs.
      - des_ifs; bsimpl; des; des_sumbool; ss; try rewrite Nat.eqb_neq in *; try rewrite Z.eqb_neq in *;
          apply_all_once Nat.eqb_eq; apply_all_once Z.eqb_eq; subst; try lia.
        + unfold update. des_ifs; econs; et.
        + unfold update. des_ifs; econs; et.
    }

    econs; ss.
    { init.
      unfold checkWf, forge, discard, put. steps.
      unfold allocF. steps. rewrite Any.upcast_downcast. steps.
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
        clear - WF WFA Heq SIM.
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
      steps.
      unfold interp_hCallE_tgt. steps. force_l. exists 0. steps.
      apply_all_once Any.upcast_inj. des; clarify. clear_tac.
      rewrite URA.unit_idl in *. rewrite GRA.padding_add in *. eapply GRA.padding_wf in _ASSUME. des.
      rename _ASSUME into WF.
      rename n into b. rename z into ofs.

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
        clear - _ASSUME.
        ss. des. do 2 spc _ASSUME0. rr in _ASSUME. des. ss.
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
      rename _ASSUME into WF.
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
    }
    econs; et.
    { init.
      unfold checkWf, forge, discard, put. steps.
      unfold cmpF. steps. rewrite Any.upcast_downcast. steps.

      assert (VALID: forall b ofs v (WF: URA.wf ((URA.black (mem_src: URA.car (t:=Mem1._memRA))) ⋅ ((b, ofs) |-> [v]))),
                 Mem.valid_ptr mem_tgt b ofs = true).
      { clear - SIM. i. cut (mem_src b ofs = inl (Some v)).
        - i. unfold Mem.valid_ptr.
          specialize (SIM b ofs). rewrite H in *. inv SIM. ss.
        - Local Transparent points_to URA.add URA.wf URA.unit.
          ss. des. specialize (WF0 b ofs). r in WF. des; clarify. ss.
          des_ifs; bsimpl; des; des_sumbool; ss; subst;
            try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
              try rewrite Z.sub_diag in *; try lia; ss.
          Local Opaque URA.add GRA.to_URA points_to URA.wf URA.unit.
      }

      des; clarify.
      - (* ptr / null *)
        clear_tac. rewrite Any.upcast_downcast in *. clarify.
        apply_all_once Any.upcast_inj. des. clarify. clear_tac.
        rewrite URA.unit_idl in *. rewrite GRA.padding_add in *. apply_all_once GRA.padding_wf. des.
        ss.
        unfold interp_hCallE_tgt. steps. force_l. exists 0. steps. force_l. esplit. force_l. esplit.
        force_l. eexists (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA))),
                          GRA.padding ((b0, ofs) |-> [v])).
        steps.
        force_l. { refl. } steps. force_l. esplit. force_l. { esplits; eauto. } steps.
        force_l. esplit. steps. force_l. { rewrite URA.unit_id. refl. } steps.
        erewrite VALID; cycle 1.
        { instantiate (1:=v). eapply _ASSUME. }
        ss. steps. esplits; eauto.
      - (* null / ptr *)
        clear_tac. rewrite Any.upcast_downcast in *. clarify.
        apply_all_once Any.upcast_inj. des. clarify. clear_tac.
        rewrite URA.unit_idl in *. rewrite GRA.padding_add in *. apply_all_once GRA.padding_wf. des.
        ss.
        unfold interp_hCallE_tgt. steps. force_l. exists 0. steps. force_l. esplit. force_l. esplit.
        force_l. eexists (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA))),
                          GRA.padding ((b0, ofs) |-> [v])).
        steps.
        force_l. { refl. } steps. force_l. esplit. force_l. { esplits; eauto. } steps.
        force_l. esplit. steps. force_l. { rewrite URA.unit_id. refl. } steps.
        erewrite VALID; cycle 1.
        { instantiate (1:=v). eapply _ASSUME. }
        ss. steps. esplits; eauto.
      - (* ptr / ptr different *)
        clear_tac. rewrite Any.upcast_downcast in *. clarify.
        apply_all_once Any.upcast_inj. des. clarify. clear_tac.
        rewrite URA.unit_idl in *. repeat rewrite GRA.padding_add in *. apply_all_once GRA.padding_wf. des.
        ss.
        unfold interp_hCallE_tgt. steps. force_l. exists 0. steps. force_l. esplit. force_l. esplit.
        force_l. eexists (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA))),
                          GRA.padding (((b0, ofs0) |-> [v0]) ⋅ ((b1, ofs1) |-> [v1]))).
        steps.
        force_l. { refl. } steps. force_l. esplit. force_l. { esplits; eauto. } steps.
        force_l. esplit. steps. force_l. { rewrite URA.unit_id. refl. } steps.
        erewrite VALID; cycle 1.
        { instantiate (1:=v0). clear - _ASSUME.
          eapply URA.wf_mon. erewrite <- URA.add_assoc. eapply _ASSUME. }
        erewrite VALID; cycle 1.
        { instantiate (1:=v1). clear - _ASSUME.
          eapply URA.wf_mon. erewrite <- URA.add_assoc.
          erewrite URA.add_comm with (a:=(b1, ofs1) |-> [v1]). eapply _ASSUME. }
        ss. steps.
        destruct (dec b0 b1); cycle 1.
        { ss. steps. esplits; eauto. }
        destruct (dec ofs0 ofs1); cycle 1.
        { ss. steps. esplits; eauto. }
        subst. clear - _ASSUME. exfalso.
        erewrite URA.add_comm in _ASSUME. eapply URA.wf_mon in _ASSUME.
        Local Transparent points_to URA.add URA.wf URA.unit.
        ss. specialize (_ASSUME b1 ofs1).
        destruct (dec b1 b1); ss. erewrite Z.leb_refl in *. ss.
        replace (ofs1 <? ofs1 + 1)%Z with true in *; ss.
        clear. symmetry. eapply Z.ltb_lt. lia.
        Local Opaque URA.add GRA.to_URA points_to URA.wf URA.unit.
      - (* ptr / ptr same *)
        clear_tac. rewrite Any.upcast_downcast in *. clarify.
        apply_all_once Any.upcast_inj. des. clarify. clear_tac.
        rewrite URA.unit_idl in *. rewrite GRA.padding_add in *. apply_all_once GRA.padding_wf. des.
        ss.
        unfold interp_hCallE_tgt. steps. force_l. exists 0. steps. force_l. esplit. force_l. esplit.
        force_l. eexists (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA))),
                          GRA.padding ((b0, ofs) |-> [v])).
        steps.
        force_l. { refl. } steps. force_l. esplit. force_l. { esplits; eauto. } steps.
        force_l. esplit. steps. force_l. { rewrite URA.unit_id. refl. } steps.
        erewrite VALID; cycle 1.
        { instantiate (1:=v). eapply _ASSUME. }
        ss. steps. esplits; eauto. destruct (dec b0 b0); ss. destruct (dec ofs ofs); ss.
        steps. esplits; eauto.
      - (* null / null *)
        clear_tac. rewrite Any.upcast_downcast in *. clarify.
        apply_all_once Any.upcast_inj. des. clarify. clear_tac.
        ss.
        unfold interp_hCallE_tgt. steps. force_l. exists 0. steps. force_l. esplit. force_l. esplit.
        force_l. eexists (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA))), (ε ⋅ c)).
        steps.
        force_l. { refl. } steps. force_l. esplit. force_l. { esplits; eauto. } steps.
        force_l. esplit. steps. force_l. { rewrite URA.add_comm. refl. } steps. esplits; eauto.
    }
    Unshelve.
    all: ss.
    all: try (by repeat econs; et).
  Qed.

End SIMMODSEM.
