Require Import Coqlib ITreelib ImpPrelude STS Behavior.
Require Import ModSem Skeleton PCM STB Open OpenDef Hoare HoareDef Imp.
Require Import Mem0 Mem1 MemOpen Mem0Openproof MemOpen0proof.
Require Import
        MWHeader
        MWCImp MWC9 MWC0 MWC1 MWC2 MWCImp8proof MWC89proof MWC90proof MWC01proof MWC12proof
        MWApp0 MWApp1 MWApp2 MWApp01proof MWApp12proof MWAppImp9proof MWApp90proof
.
Require Import MWMapImp MWMap0 MWMap1 MWMapImp0proof MWMap01proof
        Mem01proof
.

Set Implicit Arguments.



(*** TODO: move to proper place ***)
Lemma nth_error_alist_find
      `{Dec K} V kvs n (k: K) (v: V)
      (NTH: nth_error kvs n = Some (k, v))
      (NODUP: NoDup (map fst kvs))
  :
    alist_find k kvs = Some v
.
Proof.
  ginduction kvs; ii; ss.
  { destruct n; ss. }
  des_ifs.
  { apply rel_dec_correct in Heq. subst. ss. destruct n; ss.
    { clarify. }
    apply nth_error_In in NTH.
    inv NODUP. contradict H2. eapply in_map_iff. esplits; et. ss.
  }
  assert(k <> k0).
  { ii; clarify.
    assert(k0 ?[ eq ] k0 = true).
    { eapply rel_dec_correct; ss. }
    congruence.
  }
  destruct n; ss.
  { clarify. }
  inv NODUP.
  eapply IHkvs; et.
Qed.

Lemma nth_error_find_idx
      `{Dec K} V (kvs: list (K * V))
      k v n
      (NTH: nth_error kvs n = Some (k, v))
      (NODUP: NoDup (map fst kvs))
  :
    find_idx (fun '(k0, v0) => dec k k0) kvs = Some (n, (k, v))
.
Proof.
  ginduction kvs; ii; ss.
  { destruct n; ss. }
  destruct n; ss.
  - clarify. cbn. des_ifs. ss. des_sumbool. ss.
  - destruct a; ss. inv NODUP. rewrite find_idx_red. des_ifs; ss.
    + contradict H2. des_sumbool. clarify. eapply nth_error_In; et.
      erewrite map_nth_error; et; ss.
    + erewrite IHkvs; et.
Qed.






Section AUTHAUX.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG M Σ}.

(*   Lemma wf_cons *)
(*         (a0 b0 a1 b1: M) *)
(*         (WF: URA.wf (Auth.black a0 ⋅ Auth.white b0)) *)
(*     : *)
(*       URA.wf (Auth.black (a0 ⋅ a1) ⋅ Auth.white b0 ⋅ Auth.white b1) *)
(*   . *)
(*   Proof. *)
(*     ur in WF. des. *)
(*     ur. rewrite URA.unit_idl in *. esplits; et. *)
(*     cbn. *)
(*   Qed. *)

  Lemma white_add
        (a b: M)
    :
      Auth.white (a ⋅ b) = Auth.white a ⋅ Auth.white b
  .
  Proof. ur. unfold Auth.white. f_equal. ur. ss. Qed.

End AUTHAUX.





Section MEMAUX.

  Context `{@GRA.inG memRA Σ}.

  Definition _var_points_to (skenv: SkEnv.t) (var: gname) (v: val): Mem1._memRA :=
    match (skenv.(SkEnv.id2blk) var) with
    | Some  blk => _points_to (blk, 0%Z) [v]
    | None => ε
    end.

  Fixpoint _initial_points_to (sk: alist gname Sk.gdef) (csl: list gname): Mem1._memRA :=
    match csl with
    | [] => ε
    | hd :: tl =>
      match alist_find hd sk with
      | Some (Sk.Gvar iv) => (_var_points_to (Sk.load_skenv sk) hd (Vint iv)) ⋅ _initial_points_to sk tl
      | _ => ε (*** should not happen ***)
      end
    end
  .

  Lemma initial_mem_mr_cons
        sk (hd: gname) tl iv blk
        (NTH: nth_error sk blk = Some (hd, Sk.Gvar iv))
        (NIN: ~In hd tl)
        (NODUP: NoDup (map fst sk))
    :
      (initial_mem_mr (fun g => in_dec dec g (hd :: tl)) sk) =
      (initial_mem_mr (fun g => in_dec dec g tl) sk) ⋅ (_points_to (blk, 0%Z) [Vint iv])
  .
  Proof.
    extensionality b. extensionality ofs.
    ur. ur.
    destruct (dec b blk).
    - subst. unfold initial_mem_mr. rewrite NTH. ss.
      assert(In hd (hd :: tl)).
      { ss; et. }
      assert(~In hd tl).
      { ss; et. }
      des_ifs; des_sumbool; ss.
      + rewrite URA.unit_idl. rewrite _points_to_hit. ss.
      + rewrite URA.unit_idl. rewrite _points_to_miss; ss; et.
    - rewrite _points_to_miss; ss; et. rewrite URA.unit_id.
      unfold initial_mem_mr. des_ifs; des_sumbool; ss; et.
      + des; ss. subst.
        eapply NoDup_nth_error in NODUP; revgoals.
        { erewrite map_nth_error; try apply NTH; et; ss.
          erewrite map_nth_error; try apply Heq; et; ss. }
        { eapply nth_error_Some; ss. erewrite map_nth_error; et. }
        clarify.
      + Psimpl. des; ss.
  Qed.

  Lemma var_points_to_spec
        a (sk: alist gname Sk.gdef) iv blk
        (Heq: alist_find a sk = Some (Sk.Gvar iv))
        (NTH: nth_error sk blk = Some (a, Sk.Gvar iv))
        (NODUP: NoDup (map fst sk))
    :
      _var_points_to (Sk.load_skenv sk) a (Vint iv) = _points_to (blk, 0%Z) [Vint iv]
  .
  Proof.
    Local Transparent Sk.load_skenv. unfold _var_points_to. cbn.
    replace string_dec with (@dec _ string_Dec) by ss.
    erewrite nth_error_find_idx; et.
  Qed.

  Lemma initial_mem_mr_wf_aux
        sk csl
    :
      URA.wf (initial_mem_mr csl sk)
  .
  Proof.
    ur. ur. intros b ofs. unfold initial_mem_mr. des_ifs; ur; ss.
  Qed.

  Lemma initial_mem_mr_wf
        (sk: alist gname Sk.gdef)
        (csl: list gname)
        (INCL: forall g (IN: In g csl),
            exists blk iv, nth_error sk blk = Some (g, Sk.Gvar iv))
            (* exists iv, alist_find g sk = Some (Sk.Gvar iv)) *)
        (WF: Sk.wf sk)
        (NODUP: NoDup csl)
    :
      URA.wf ((Auth.black (initial_mem_mr (fun g => in_dec dec g csl) sk))
                ⋅ Auth.white (_initial_points_to sk csl))
  .
  Proof.
    erewrite URA.unfold_wf. cbn. rewrite URA.unfold_add. cbn. esplits; et.
    - rewrite URA.unit_idl.
      induction csl.
      { ss. r. esplits. rewrite URA.unit_idl. refl. }
      exploit INCL. { ss; et. } i; des.
      erewrite initial_mem_mr_cons; et; cycle 1.
      { inv NODUP; ss. }
      dup x. eapply nth_error_alist_find in x; ss. des_ifs.
      erewrite var_points_to_spec; et.
      rewrite URA.add_comm.
      eapply URA.extends_add.
      eapply IHcsl; et.
      inv NODUP; ss.
    - eapply initial_mem_mr_wf_aux.
  Qed.

  Lemma unfold_var_points_to
        ske g v
    :
      var_points_to ske g v = Auth.white (_var_points_to ske g v)
  .
  Proof. unfold var_points_to, _var_points_to. des_ifs. Qed.

End MEMAUX.



Section GRAAUX.

  Inductive wf_res: Type := mk_wf_res { wr_M: URA.t; wr_res: wr_M; wr_pf: URA.wf wr_res }.
  Definition wf_res_empty: wf_res := @mk_wf_res (of_RA.t RA.empty) ε URA.wf_unit.

  Variable wrs: list wf_res.

  Let Σ: GRA.t := GRA.of_list (map wr_M wrs).

  Definition nth_res (n: nat): Σ.
    { set (w := nth n wrs wf_res_empty).
      eapply (@GRA.embed w.(wr_M)); cycle 1.
      { eapply w.(wr_res). }
      subst Σ. unfold GRA.of_list.
      econs; et. instantiate (1:=n).
      change (of_RA.t RA.empty) with (wr_M wf_res_empty).
      rewrite map_nth. ss.
    }
  Defined.

  Lemma nth_res_wf: forall n, URA.wf (nth_res n).
  Proof.
    unfold nth_res. i. set (nth n wrs wf_res_empty) as x.
    assert(URA.wf (wr_res x)).
    { eapply wr_pf. }
    eapply GRA.wf_embed; ss.
  Qed.

  Lemma nth_res_excl: forall n m (NE: n <> m), (nth_res n) m = ε.
  Proof.
    unfold nth_res. i.
    Local Transparent GRA.to_URA.
    unfold GRA.embed. des_ifs.
  Qed.

  Fixpoint summing (n: nat): Σ :=
    match n with
    | 0 => nth_res n
    | S m => nth_res n ⋅ summing m
    end
  .

  Lemma summing_unit: forall (k l: nat) (LT: k < l), summing k l = ε.
  Proof.
    {
      intro k. induction k; ii; ss.
      { unfold nth_res. unfold GRA.embed. cbn. des_ifs. lia. }
      ur. rewrite IHk; try lia. rewrite URA.unit_id.
      rewrite nth_res_excl; ss. lia.
    }
  Qed.

  Lemma summing_eq: forall (k: nat), summing k k = nth_res k k.
  Proof.
    induction k.
    { ss. }
    ss. ur. rewrite summing_unit; try lia. rewrite URA.unit_id. ss.
  Qed.

  Lemma wf_res_wf
        n
    :
      URA.wf (summing n)
  .
  Proof.
    induction n; ii; ss.
    { eapply nth_res_wf. }
    ur. i. destruct (dec (S n) k).
    - subst. rewrite summing_unit; try lia. rewrite URA.unit_id.
      hexploit (@nth_res_wf (S n)). intro T. ur in T. et.
    - rewrite nth_res_excl; try lia. rewrite URA.unit_idl. ur in IHn. ss.
  Qed.

End GRAAUX.













Definition MWGRA: GRA.t := GRA.of_list [Mem1.memRA; spRA; mwRA; AppRA.t].
Local Existing Instance MWGRA.

Instance memRA_inG: @GRA.inG Mem1.memRA MWGRA.
Proof. exists 0. ss. Defined.
Local Existing Instance memRA_inG.

Instance spRA_inG: @GRA.inG spRA MWGRA.
Proof. exists 1. ss. Defined.
Local Existing Instance spRA_inG.

Instance mwRA_inG: @GRA.inG mwRA MWGRA.
Proof. exists 2. ss. Defined.
Local Existing Instance mwRA_inG.

Instance AppRA_inG: @GRA.inG AppRA.t MWGRA.
Proof. exists 3. ss. Defined.
Local Existing Instance AppRA_inG.

Lemma high_init_wf
      (x: Mem1._memRA)
      (WF: URA.wf x)
  :
    URA.wf
      (GRA.embed Init ⋅ GRA.embed Run ⋅ (GRA.embed (mw_state (λ _, None)) ⋅ GRA.embed (mw_stateX (λ _, None)))
                 ⋅ (GRA.embed sp_black ⋅ GRA.embed sp_white) ⋅ (GRA.embed (Auth.black x))).
Proof.
  rewrite ! GRA.embed_add.
  unshelve evar (P0: wf_res).
  { apply (@mk_wf_res AppRA.t (Init ⋅ Run)). ur. ss. }
  unshelve evar (P1: wf_res).
  { apply (@mk_wf_res spRA (sp_black ⋅ sp_white)). ur. ss. esplits; ur; ss; et. des_ifs. refl. }
  unshelve evar (P2: wf_res).
  { apply (@mk_wf_res memRA (Auth.black x)). ur. esplits; ss.
    { r. esplits; et. rewrite URA.unit_idl; ss. }
  }
  unshelve evar (P3: wf_res).
  { apply (@mk_wf_res mwRA (mw_state (λ _, None) ⋅ mw_stateX (λ _, None))).
    ur. rewrite URA.unit_id. esplits; ss.
    { refl. }
    { ur. ss. }
  }
  hexploit (@wf_res_wf [P2;P1;P3;P0] 4). intro T. ss. unfold nth_res in *. cbn in *.
  rewrite embed_unit in T. rewrite URA.unit_idl in T.
  subst P0 P1 P2 P3.
  r_wf T. clear T.
  f_equal.
  { f_equal. unfold AppRA_inG. f_equal. eapply proof_irr. }
  f_equal.
  { f_equal. unfold mwRA_inG. f_equal. eapply proof_irr. }
  f_equal.
  { f_equal. unfold spRA_inG. f_equal. eapply proof_irr. }
  { f_equal. unfold memRA_inG. f_equal. eapply proof_irr. }
Qed.




Let CSL0: gname -> bool := fun g => in_dec dec g ["gv0"; "gv1"; "initialized"].

Section MWIMPL.
  Definition mw_impl := [Mem0.Mem (fun _ => false); MWCImp.MW; MWAppImp.App; MWMapImp.Map].
  Definition mw_impl_itr: itree eventE Any.t := ModSemL.initial_itr (ModL.enclose (Mod.add_list mw_impl)) None.
End MWIMPL.

Section MWABS.
  Definition mw_abs :=
    [SMod.to_src (SMem (negb ∘ CSL0)); SMod.to_src MWC2.SMW; SMod.to_src MWApp2.SApp; SMod.to_src MWMap1.SMap].
  Definition mw_abs_itr: itree eventE Any.t := ModSemL.initial_itr (ModL.enclose (Mod.add_list mw_abs)) None.
End MWABS.



Section PROOF.

  Let MWLow: refines2 [Mem0.Mem (fun _ => false); MWCImp.MW; MWAppImp.App] [Mem0.Mem CSL0; MWC0.MW; MWApp0.App].
  Proof.
    transitivity (KMod.transl_tgt_list [KMem CSL0 CSL0; MWC9.KMW; MWApp9.KApp]).
    { eapply refines2_cons.
      { eapply Mem0Openproof.correct. ii; ss. }
      eapply refines2_cons.
      - etrans.
        { eapply MWCImp8proof.correct. }
        eapply MWC89proof.correct. i.
        ii. unfold to_closed_stb.
        autounfold with stb in *. autorewrite with stb in *. cbn in FIND.
        rewrite ! eq_rel_dec_correct in *. des_ifs.
      - eapply MWAppImp9proof.correct. i.
        ii. unfold to_closed_stb.
        autounfold with stb in *. autorewrite with stb in *. cbn in FIND.
        rewrite ! eq_rel_dec_correct in *. des_ifs.
    }
    etrans.
    { eapply adequacy_open. i. exists ε. split.
      { cbn. rewrite ! URA.unit_idl. rewrite ! GRA.embed_add. apply GRA.wf_embed.
        assert(FIND0: alist_find "gv0" sk = Some (Sk.Gvar 0)).
        { exploit (SKINCL "gv0"); et. { ss. eauto 10. } intro T. eapply In_nth_error in T. des; et.
          eapply nth_error_alist_find; et. }
        assert(FIND1: alist_find "gv1" sk = Some (Sk.Gvar 0)).
        { exploit (SKINCL "gv1"); et. { ss. eauto 10. } intro T. eapply In_nth_error in T. des; et.
          eapply nth_error_alist_find; et. }
        assert(FIND2: alist_find "initialized" sk = Some (Sk.Gvar 0)).
        { exploit (SKINCL "initialized"); et. { ss. eauto 10. } intro T. eapply In_nth_error in T. des; et.
          eapply nth_error_alist_find; et. }
        hexploit (@initial_mem_mr_wf sk ["gv0"; "gv1"; "initialized"]); et.
        { ii. ss. des; clarify.
          - exploit (SKINCL "gv0"); et. { ss. eauto 10. } intro T. eapply In_nth_error in T. des; et.
          - exploit (SKINCL "gv1"); et. { ss. eauto 10. } intro T. eapply In_nth_error in T. des; et.
          - exploit (SKINCL "initialized"); et. { ss. eauto 10. } intro T. eapply In_nth_error in T. des; et.
        }
        { ImpProofs.solve_NoDup. }
        i. ss. des_ifs. rewrite URA.unit_id in H.
        rewrite ! white_add in H. rewrite <- ! unfold_var_points_to in H.
        rewrite ! URA.add_assoc in *. rewrite ! URA.add_assoc in H. ss. }
      ii. ss. clarify. esplits; et; ss.
      { rr. uipropall. }
      { ii. rr in POST. uipropall. }
    }
    eapply refines2_cons.
    { eapply MemOpen0proof.correct. }
    { eapply refines2_cons.
      - eapply MWC90proof.correct.
      - eapply MWApp90proof.correct. }
  Unshelve.
    all: ss.
  Qed.

  Let gstb := MWHeader.MWStb ++ MapStb ++ Mem1.MemStb ++ AppStb.

  Let MWMap: refines2 [MWMapImp.Map] [MWMap1.Map (fun _ => to_stb gstb)].
  Proof.
    etrans.
    eapply MWMapImp0proof.correct.
    eapply MWMap01proof.correct.
    subst gstb. i. stb_incl_tac; eauto 20.
  Qed.

  Definition refines2_closed (md_tgt md_src: list Mod.t): Prop :=
    refines_closed (Mod.add_list md_tgt) (Mod.add_list md_src)
  .

   Lemma refines2_close: refines2 <2= refines2_closed.
   Proof. ii. specialize (PR nil). ss. unfold Mod.add_list in *. ss. rewrite ! ModL.add_empty_l in PR. eauto. Qed.

   Global Program Instance refines2_closed_PreOrder: PreOrder refines2_closed.
   Next Obligation.
     ii. ss.
   Qed.
   Next Obligation.
     ii. eapply H in PR. eapply H0 in PR. eapply PR.
   Qed.

   Require Import Weakening.

   Lemma gstb_weaker: forall sk,
       stb_weaker (to_stb (MWHeader.MWStb ++ AppStb ++ MWHeader.MapStb ++ Mem1.MemStb))
                  ((λ _ : Sk.t, to_stb gstb) sk).
   Proof.
     ii. unfold gstb. stb_tac. rewrite ! eq_rel_dec_correct in *.
     repeat match goal with
            | H: context[ match (string_Dec ?x ?y) with _ => _ end ] |- _ =>
              destruct (string_Dec x y);
                [subst; ss; clarify;
                 try by (esplits; et; [stb_tac|]; et; try refl)|]
            end.
     ss.
   Qed.

   (* Mem0.Mem (fun _ => true) *)
   Theorem MW_correct:
     refines2_closed (mw_impl) (mw_abs).
   Proof.
     unfold mw_impl, mw_abs.
     etrans.
     { eapply refines2_close.
       change [Mem0.Mem (λ _, false); MWCImp.MW; MWAppImp.App; MWMapImp.Map] with
           ([Mem0.Mem (λ _, false); MWCImp.MW; MWAppImp.App] ++ [MWMapImp.Map]).
       eapply refines2_app; try eassumption.
     }
     etrans.
     { eapply refines2_close.
       eapply refines2_cons.
       { etrans; [eapply Mem01proof.correct|]. unfold Mem1.Mem. eapply adequacy_weaken.
         instantiate (1:=fun _ => to_stb gstb). i. r. i. ss.
       }
       eapply refines2_cons.
       { etrans; [eapply MWC01proof.correct|]. etrans; [eapply MWC12proof.correct|].
         eapply adequacy_weaken. eapply gstb_weaker. }
       eapply refines2_cons.
       { etrans; [eapply MWApp01proof.correct|]. etrans; [eapply MWApp12proof.correct|].
         { i. instantiate (1:=fun _ => to_stb gstb). unfold gstb. stb_incl_tac; ss; eauto 10. }
         refl.
       }
       refl.
     }
     unfold App, Map.
     (* set (SMod.to_tgt (to_stb ∘ SMod.get_stb)) as f in *. *)
     set (SMod.to_tgt (λ _, to_stb gstb)) as f in *.
     etrans.
     { change [f (SMem (negb ∘ CSL0)); f SMW; f SApp; f SMap] with
           (map f [(SMem (negb ∘ CSL0)); SMW; SApp; SMap]).
       r.
       assert((λ _ : Sk.t, to_stb gstb) = (to_stb ∘ SMod.get_stb [SMem (negb ∘ CSL0); SMW; SApp; SMap])).
       { extensionality sk. unfold gstb.
         autounfold with stb; autorewrite with stb. cbn. extensionality fn. cbn.
         rewrite ! eq_rel_dec_correct.
         repeat match goal with
                | |- context[ match (string_Dec ?x ?y) with _ => _ end ] =>
                  destruct (string_Dec x y);
                    [subst; ss; clarify;
                     try by (r in PURE; des; ss; unfold is_pure in *; des_ifs;
                             r in PURE; uipropall; des; clarify; r in PURE1; uipropall; des; clarify);
                     try by (stb_tac; ss)|]
                end.
         ss.
       }
       subst f. rewrite H. eapply adequacy_type; cycle 1.
       - i. stb_tac. clarify. ss. exists tt.
         instantiate (1:=GRA.embed Init ⋅ GRA.embed (mw_stateX Maps.empty) ⋅ GRA.embed sp_white).
         esplits; ss; et.
         + iIntros "[[A B] C]".  iFrame. iSplits; ss; et.
         + i. iIntros "[A %]". subst. ss.
       - ss. cbn. rewrite ! URA.unit_id. rewrite ! URA.unit_idl.
         match goal with
         | [ |- context[Auth.black ?f] ] => set f as x in *
         end.
         erewrite f_equal.
         { eapply high_init_wf. instantiate (1:=x). subst x. eapply initial_mem_mr_wf_aux. }
         r_solve.
     }
     refl.
   Qed.

End PROOF.

Require Import SimSTS2 Imp2Csharpminor Imp2Asm.
Require Import Imp2AsmProof.
Section PROOF.
  Context `{builtins : builtinsTy}.
  Let mw_imp := [MWprog; MWAppImp.Appprog; Map_prog].
  Hypothesis source_linking: exists imp, link_imps mw_imp = Some imp.

  Theorem echo_compile_correct
          (asms : Coqlib.nlist Asm.program)
          (COMP: Forall2 (fun imp asm => compile_imp imp = Errors.OK asm) mw_imp asms)
    :
      exists asml, (Linking.link_list asms = Some asml) /\
                   (improves2_program (ModL.compile (Mod.add_list mw_abs)) (Asm.semantics asml)).
  Proof.
    hexploit compile_behavior_improves; [et|et|]. i. des. esplits; [et|].
    eapply improves_combine; [|et]. eapply MW_correct.
  Qed.
End PROOF.
