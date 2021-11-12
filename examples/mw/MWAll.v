Require Import Coqlib ITreelib ImpPrelude STS Behavior.
Require Import ModSem Skeleton PCM STB Open OpenDef Hoare HoareDef Imp.
Require Import Mem0 Mem1 MemOpen Mem0Openproof MemOpen0proof.
Require Import
        MWHeader
        MWCImp MWC9 MWC0 MWC1 MWC2 MWCImp9proof MWC90proof MWC01proof MWC12proof
        MWApp0 MWApp1 MWApp2 MWApp01proof MWApp12proof MWAppImp9proof MWApp90proof
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





Section PROOF.

  Let CSL0: gname -> bool := fun g => in_dec dec g ["gv0"; "gv1"; "initialized"].
  Let MWLow: refines2 [Mem0.Mem (fun _ => false); MWCImp.MW; MWAppImp.App] [Mem0.Mem CSL0; MWC0.MW; MWApp0.App].
  Proof.
    transitivity (KMod.transl_tgt_list [KMem CSL0 CSL0; MWC9.KMW; MWApp9.KApp]).
    { eapply refines2_cons.
      { eapply Mem0Openproof.correct. ii; ss. }
      eapply refines2_cons.
      - eapply MWCImp9proof.correct. i.
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
      ii. ss.
    }
    eapply refines2_cons.
    { eapply MemOpen0proof.correct. }
    { eapply refines2_cons.
      - eapply MWC90proof.correct.
      - eapply MWApp90proof.correct. }
  Qed.

  Require Import MWMapImp MWMap0 MWMap1 MWMapImp0proof MWMap01proof
          Mem01proof
  .

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

   Theorem MW_correct:
     refines2_closed
       ([Mem0.Mem (fun _ => false); MWCImp.MW; MWAppImp.App; MWMapImp.Map])
       ([Mem0.Mem (fun _ => true); SMod.to_src MWC2.SMW; SMod.to_src MWApp2.SApp; SMod.to_src MWMap1.SMap]).
   Proof.
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
       - i. stb_tac. ss.
     }
         des_ifs.
         repeat replace string_dec with (@dec _ string_Dec) by ss.
         des_ifs.
       eapply adequacy_type2.
       - econs.
       eapply adequacy_type.

       
       instantiate (1:=(map f [(SMem (negb ∘ CSL0)); SMW; SApp; SMap])). refl. }
       repeat (
           match goal with | [ |- context[?a :: ?b :: ?c] ] => rewrite (@cons_app _ a (b :: c)) end;
           match goal with
           | [ |- context[[SMod.to_tgt ?f ?a]] ] =>
             change ([SMod.to_tgt f a]) with (map (SMod.to_tgt f) [a])
           end).
       multimatch goal with
       | [ |- context[(map ?f ?a) ++ (map _ ?b)] ] => idtac a; idtac b
       end.
       (map _ _)
       erewrite <- map_app with (f:=SMod.to_tgt (λ _ : Sk.t, to_stb gstb)).
     }
     unfold MW. unfold App.
     unfold Map.
     replace [Mem1.Mem (negb ∘ CSL0)] with [Mem1.Mem (negb ∘ CSL0)].
     replace [Mem1.Mem (negb ∘ CSL0); MW; App (λ _, to_stb gstb); Map (λ _, to_stb gstb)] with
         [Mem1.Mem (negb ∘ CSL0); MW; App (λ _, to_stb gstb); Map (λ _, to_stb gstb)].
     etrans.
     { r. eapply adequacy_type.
       [Mem1.Mem (negb ∘ CSL0); MW; App (λ _ : Sk.t, to_stb gstb); Map (λ _ : Sk.t, to_stb gstb)]
         (map (SMod.to_tgt (to_stb ∘ SMod.get_stb mds)) mds)
         TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT
       -
       -
       { et.
         change [Mem0.Mem CSL0; SMod.to_src SMW; SMod.to_src SApp; SMod.to_src SMap] with
             ([Mem0.Mem CSL0; SMod.to_src SMW; SMod.to_src SApp] ++ [SMod.to_src SMap]).
         eapply refines2_app; cycle 1.
         { eapply MWMap.
         Qed.
         TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT

  Theorem MW_correct:
    refines2_closed (Mod.add_list [Mem0.Mem (fun _ => false); MWCImp.MW; MWAppImp.App])
                   (Mod.add_list [Mem0.Mem CSL0; SMod.to_src MWC2.SMW; SMod.to_src MWApp2.SApp; MWMap1.Map (fun _ => to_stb gstb)]).
  Proof.
    etrans.
    {
    eapply .
  Qed.

  Theorem MW: refines2 [MWMapImp.Map] [MWMap1.Map (fun _ => to_stb gstb)].
  Proof.
    etrans.
    eapply MWMapImp0proof.correct.
    eapply MWMap01proof.correct.
    subst gstb. i. stb_incl_tac; eauto 20.
  Qed.
  (* Let CSL0: gname -> bool := fun g => in_dec dec g ["gv0"; "gv1"]. *)
  (* Let MWLow: refines2 [Mem0.Mem (fun _ => false); MWCImp.MW] [Mem0.Mem CSL0; MWC0.MW]. *)
  (* Proof. *)
  (*   transitivity (KMod.transl_tgt_list [KMem CSL0 CSL0; MWC9.KMW]). *)
  (*   { eapply refines2_cons. *)
  (*     { eapply Mem0Openproof.correct. ii; ss. } *)
  (*     { eapply MWCImp9proof.correct. *)
  (*       i. *)
  (*       ii. unfold to_closed_stb. *)
  (*       autounfold with stb in *. autorewrite with stb in *. cbn in *. *)
  (*       rewrite ! eq_rel_dec_correct in *. des_ifs. *)
  (*     } *)
  (*   } *)
  (*   etrans. *)
  (*   { eapply adequacy_open. i. exists ε. split. *)
  (*     { g_wf_tac. *)
  (*       { Local Transparent Sk.load_skenv _points_to string_dec. *)
  (*         (* Eval compute in (KMod.get_sk [KMem CSL0 CSL0; KMW]). *) *)
  (*         replace (KMod.get_sk [KMem CSL0 CSL0; KMW]) with *)
  (*                 [("get", Sk.Gfun); ("gv0", Sk.Gvar 0); ("gv1", Sk.Gvar 0); ("gv2", Sk.Gvar 0); *)
  (*                  ("gv3", Sk.Gvar 0); ("loop", Sk.Gfun); ("put", Sk.Gfun)] in * by refl. *)
  (*         dup SKINCL. dup SKWF. *)
  (*         eapply Sk.incl_incl_env in SKINCL. eapply Sk.load_skenv_wf in SKWF. *)
  (*         hexploit (SKINCL "gv0"). { ss. eauto. } intros [blk0 FIND0]. *)
  (*         hexploit (SKINCL "gv1"). { ss. eauto. } intros [blk1 FIND1]. *)
  (*         ur. unfold var_points_to. des_ifs. des; clarify. *)
  (*         rewrite URA.unit_idl. unfold points_to, Auth.white in *. *)
  (*         Opaque _points_to SkEnv.id2blk. clarify. *)
  (*         esplits. *)
  (*         - r. exists ε. *)
  (*           extensionality b. extensionality ofs. *)
  (*           unfold initial_mem_mr. *)
  (*           des_ifs. *)
  (*           { assert(s <> "gv0"). *)
  (*             { ii; clarify. *)
  (*               exploit (SKINCL0 "gv0"); ss; et. intro T. *)
  (*               eapply nth_error_In in Heq. *)
  (*               r in SKWF0. ss. *)
  (*               eapply NoDup_inj_aux; [eassumption| |apply Heq|apply T|..]; ss. *)
  (*             } *)
  (*             assert(s <> "gv1"). *)
  (*             { ii; clarify. *)
  (*               exploit (SKINCL0 "gv1"); ss; et. intro T. *)
  (*               eapply nth_error_In in Heq. *)
  (*               r in SKWF0. ss. *)
  (*               eapply NoDup_inj_aux; [eassumption| |apply Heq|apply T|..]; ss. *)
  (*             } *)
  (*             assert(SkEnv.id2blk (Sk.load_skenv sk) s = Some b). *)
  (*             { Local Transparent SkEnv.id2blk. *)
  (*               clear - Heq. cbn. uo. des_ifs. *)
  (*               - admit "somehow?". *)
  (*               - admit "somehow?". *)
  (*             } *)
  (*             assert(b <> blk0). *)
  (*             { ii. clarify. admit "somehow?". } *)
  (*             assert(b <> blk1). *)
  (*             { ii. clarify. admit "somehow?". } *)
  (*             admit "somehow?". *)
  (*           } *)
  (*           { admit "???". } *)
  (*           { admit "???". } *)
  (*           { admit "???". } *)
  (*           { admit "???". } *)
  (*         - { admit "???". } *)
  (*       } *)
  (*     } *)
  (*     ii. ss. clarify. ss. esplits; ss; et. *)
  (*     - rr. uipropall. *)
  (*     - ii. rr in POST. uipropall. *)
  (*   } *)
  (*   eapply refines2_cons. *)
  (*   { eapply MemOpen0proof.correct. } *)
  (*   { eapply MWC90proof.correct. } *)
  (* Qed. *)





  (* Section AUX. *)
  (*   Context {CONF: EMSConfig}. *)
  (*   Context `{Sk.ld}. *)

  (*   Lemma refines2_comm_l *)
  (*         ma mb mc *)
  (*     : *)
  (*       refines2 (ma ++ mb) mc = refines2 (mb ++ ma) mc *)
  (*   . *)
  (*   Proof. *)
  (*     eapply Axioms.prop_ext. *)
  (*     split; i. *)
  (*     - ii. eapply H0; clear H0. rewrite Mod.add_list_app in *. *)
  (*       set (Mod.add_list ctx) as c in *. *)
  (*       set (Mod.add_list ma) as a in *. *)
  (*       set (Mod.add_list mb) as b in *. *)
  (*       rewrite ModL.add_assoc in *. *)
  (*       rewrite ModL.add_assoc_rev in *. *)
  (*       eapply ModL.add_comm. *)
  (*       rewrite ModL.add_assoc_rev in *. *)
  (*       eapply ModL.add_comm. ss. eapply ModL.add_comm in eapply H0. rewrite ModL.add_comm in *. r in H0. r. *)
  (*   Qed. *)
  (* End AUX. *)
    eapply refines2
    cbn.
    refl.
                -
                ss. r. unfold SkEnv.id2blk.
              assert(b <> blk0).
              { ii; clarify.
                exploit (SKINCL0 "gv0"); ss; et. intro T.
                eapply nth_error_In in Heq.
                r in SKWF0. ss.
                eapply NoDup_inj_aux; [eassumption| |apply Heq|..]; ss.
              }
              { ii. clarify.
                {
              ss.
            Transparent _points_to.
            extensionality b. extensionality ofs.
            unfold initial_mem_mr.
            des_ifs.
            extensionality b. extensionality ofs.

            etrans.
            { instantiate (1:=initial_mem_mr CSL0 [("get", Sk.Gfun); ("gv0", Sk.Gvar 0); ("gv1", Sk.Gvar 0);
                                                   ("gv2", Sk.Gvar 0); ("gv3", Sk.Gvar 0); ("loop", Sk.Gfun);
                                                   ("put", Sk.Gfun)]).
              r. exists ε. rewrite URA.unit_id.
              extensionality b. extensionality ofs.
              destruct b.
              { cbn. ur. ur. cbn.
              ur. extensionality b.
              ur. extensionality ofs.
              ur.
              unfold initial_mem_mr.
              destruct b; ss.
              des_ifs; bsimpl; des; des_sumbool.
              extensionality b. extensionality ofs.
              ur.
            }
            r. exists ε. rewrite URA.unit_id.
            ur. extensionality b.
            ur. extensionality ofs.
            ur.
            unfold initial_mem_mr.
            des_ifs; bsimpl; des; des_sumbool.
            extensionality b. extensionality ofs.
            ur.
            ss.
          -
          ur. ss.


          intros [blk1 FIND1].
          cbn. eauto. [cbn; eauto|]. intros G0.
          hexploit (SKINCL "gv1"); ss; eauto. intros G1.
          ur. unfold var_points_to. des_ifs.
          { admit "". }
          { exfalso. cbn in *.
          unfold initial_mem_mr.

          des_ifs. ss. uo. split.
          2: { ur. i. ur. i. ur. des_ifs. }
          { repeat rewrite URA.unit_id. ur. eexists ε.
            repeat rewrite URA.unit_id. extensionality k. extensionality n.
            unfold sumbool_to_bool, andb. des_ifs.
            { ss. clarify. }
            { ss. clarify. exfalso. lia. }
            { repeat (destruct k; ss). }
          }
        }
        Local Transparent Sk.load_skenv _points_to string_dec.
        unfold var_points_to.
        rewrite URA.unit_idl.
        ur. unfold var_points_to, initial_mem_mr. ss. uo. idtac. split.
        2: { ur. i. ur. i. ur. des_ifs. }
        { repeat rewrite URA.unit_id. ur. eexists ε.
          repeat rewrite URA.unit_id. extensionality k. extensionality n.
          unfold sumbool_to_bool, andb. des_ifs.
          { ss. clarify. }
          { ss. clarify. exfalso. lia. }
          { repeat (destruct k; ss). }
        }
      }

      { g_wf_tac. repeat (i; splits; ur; ss). refl. }
      { ii. ss. }
    }

    
          eapply incl_appl.
        cbn. rr. unfold to_stb_context, to_stb. ii. ss. stb_tac.
        des_ifs.
        apply_all_once rel_dec_correct. subst.
        Local Transparent
        unfold rel_dec in *. des_ifs.
        unfold to_stb_context. unfold to_closed_stb. ss.
        etrans; [|eapply to_closed_stb_weaker]. stb_incl_tac; try tauto. }
        i. ss. refl. }
      eapply MWCImp9proof.correct.
      etrans.
      { eapply MWCImp9proof.correct. refl. }
      { unfold MWC9.MW. Set Printing Implicit. Unset Printing Notations. Set Printing All. unfold KMW.
        (@to_closed_stb MWGRA ∘ @KMod.get_stb MWGRA [@KMem MWGRA memRA_inG; @KMW MWGRA memRA_inG])
        TTTTTTTTTTTTTTT
        eapply MWC90proof.correct.

      
      eapply refines2_cons; [|refl].
      { etrans.
        { eapply StackImp0proof.correct. }
        { eapply Stack01proof.correct. i.
          etrans; [|eapply to_closed_stb_weaker]. stb_incl_tac; tauto. }
      }
    }

    {
    }
    etrans.
    { eapply adequacy_open. i. exists ε. split.
      { g_wf_tac. repeat (i; splits; ur; ss). refl. }
      { ii. ss. }

    }
  Qed.

  Theorem mw_correct:
    refines2 [Mem0.Mem; MWCImp.MW.Stack; EchoImp.Echo]
             [Mem0.Mem; Stack2.Stack; KMod.transl_src (fun _ => ["Echo"]) KEcho].
  Proof.
  Qed.
End PROOF.



(* Imp program *)
Require Import Mem0 StackImp EchoImp EchoMainImp ClientImp.
Section ECHOIMP.
  Definition echo_progs := [Stack_prog; Echo_prog; EchoMain_prog; Client_prog].
  Definition echo_imp: ModL.t :=
    Mod.add_list (Mem :: map ImpMod.get_mod echo_progs).

  Definition echo_imp_itr := ModSemL.initial_itr (ModL.enclose echo_imp) None.
End ECHOIMP.


Require Import Mem0 Stack0 Echo0 EchoMain0 Client0.
Section ECHOIMPL.
  Definition echo_impl: ModL.t :=
    Mod.add_list [Mem; Stack; Echo; Main; Client].

  Definition echo_impl_itr := ModSemL.initial_itr (ModL.enclose echo_impl) None.
End ECHOIMPL.


Require Import MemOpen Stack3A Echo1 EchoMain0 Client0.
(* spec program *)
Require Import Stack2.
Section ECHOSPEC.
  Definition echo_spec: ModL.t :=
    Mod.add_list [
        Mem0.Mem;
      Stack2.Stack;
      KMod.transl_src (fun _ => ["Echo"]) KEcho;
      Main; Client
      ].

  Definition echo_spec_itr := ModSemL.initial_itr (ModL.enclose echo_spec) None.
End ECHOSPEC.



Require Import Mem0Openproof MemOpen0proof.
Require Import StackImp0proof Stack01proof Stack12proof Stack23Aproof.
Require Import EchoMainImp0proof EchoImp0proof.
Require Import ClientImp0proof Echo01proof.
Require Import Echo1mon Stack32proof.
Section PROOF.
  Theorem echo_correct:
    refines2 [Mem0.Mem; StackImp.Stack; EchoImp.Echo]
             [Mem0.Mem; Stack2.Stack; KMod.transl_src (fun _ => ["Echo"]) KEcho].
  Proof.
    transitivity (KMod.transl_tgt_list [KMem; Stack1.KStack]++[EchoImp.Echo]).
    { eapply refines2_cons.
      { eapply Mem0Openproof.correct. }
      eapply refines2_cons; [|refl].
      { etrans.
        { eapply StackImp0proof.correct. }
        { eapply Stack01proof.correct. i.
          etrans; [|eapply to_closed_stb_weaker]. stb_incl_tac; tauto. }
      }
    }
    etrans.
    { eapply refines2_app; [|refl].
      eapply adequacy_open. i. exists ε. split.
      { g_wf_tac. repeat (i; splits; ur; ss). refl. }
      { ii. ss. }
    }
    eapply refines2_cons.
    { eapply MemOpen0proof.correct. }
    transitivity (KMod.transl_tgt_list [Stack3A.KStack; KEcho]).
    { eapply refines2_cons.
      { etrans.
        { eapply Stack12proof.correct. }
        { eapply Stack23Aproof.correct. }
      }
      { etrans.
        { eapply EchoImp0proof.correct. }
        { eapply Echo01proof.correct.
          stb_context_incl_tac; tauto. }
      }
    }
    etrans.
    { eapply adequacy_open. i. exists ε. split.
      { g_wf_tac; repeat (i; splits; ur; ss). refl. }
      { ii. ss. }
    }
    { eapply refines2_cons.
      { eapply Stack32proof.correct. }
      eapply refines2_cons; [|refl].
      { eapply Echo1mon.correct. ii. ss. des; auto. }
    }
  Qed.

  Corollary echo_closed_correct:
    refines_closed echo_imp echo_spec.
  Proof.
    eapply refines_close. hexploit refines2_app.
    { eapply echo_correct. }
    { eapply refines2_cons.
      { eapply EchoMainImp0proof.correct. }
      { eapply ClientImp0proof.correct. }
    }
    ss.
  Qed.
End PROOF.


Require Import SimSTS2 Imp2Csharpminor Imp2Asm.
Require Import Imp2AsmProof.
Section PROOF.
  Context `{builtins : builtinsTy}.
  Hypothesis source_linking: exists impl, link_imps echo_progs = Some impl.

  Theorem echo_compile_correct
          (asms : Coqlib.nlist Asm.program)
          (COMP: Forall2 (fun imp asm => compile_imp imp = Errors.OK asm) echo_progs asms)
    :
      exists asml, (Linking.link_list asms = Some asml) /\
                   (improves2_program (ModL.compile echo_spec) (Asm.semantics asml)).
  Proof.
    hexploit compile_behavior_improves; [et|et|]. i. des. esplits; [et|].
    eapply improves_combine; [|et]. eapply echo_closed_correct.
  Qed.
End PROOF.
