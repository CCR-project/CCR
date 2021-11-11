Require Import Coqlib ITreelib ImpPrelude STS Behavior.
Require Import ModSem Skeleton PCM STB Open OpenDef Hoare HoareDef Imp.
Require Import Mem0 Mem1 MemOpen Mem0Openproof MemOpen0proof.
Require Import
        MWHeader
        MWCImp MWC9 MWC0 MWC1 MWC2 MWCImp9proof MWC90proof MWC01proof MWC12proof
        MWApp0 MWApp1 MWApp2 MWApp01proof MWApp12proof MWAppImp9proof MWApp90proof
.

Set Implicit Arguments.



Definition MWGRA: GRA.t := GRA.of_list [Mem1.memRA; spRA; mapRA; mwRA; AppRA.t].
Local Existing Instance MWGRA.

Instance memRA_inG: @GRA.inG Mem1.memRA MWGRA.
Proof. exists 0. ss. Defined.
Local Existing Instance memRA_inG.

Instance spRA_inG: @GRA.inG spRA MWGRA.
Proof. exists 1. ss. Defined.
Local Existing Instance spRA_inG.

Instance mapRA_inG: @GRA.inG mapRA MWGRA.
Proof. exists 2. ss. Defined.
Local Existing Instance mapRA_inG.

Instance mwRA_inG: @GRA.inG mwRA MWGRA.
Proof. exists 3. ss. Defined.
Local Existing Instance mwRA_inG.

Instance AppRA_inG: @GRA.inG AppRA.t MWGRA.
Proof. exists 4. ss. Defined.
Local Existing Instance AppRA_inG.

Section PROOF.

(* (*   Check (to_stb_context ["new"; "access"; "update"; "init"; "run"] (MWStb ++ MemStb)). *) *)
(* (*   Check (@to_closed_stb MWGRA ∘ @KMod.get_stb MWGRA [@KMem MWGRA memRA_inG; @KMW MWGRA memRA_inG]). *) *)
(*   Let abc_correct : *)
(* ∀ (Σ : GRA.t) (H : GRA.inG memRA Σ) (global_stb : Sk.t -> string → option HoareDef.fspec), *)
(*   (forall sk, stb_incl (to_stb_context ["new"; "access"; "update"; "init"; "run"] (MemStb)) (global_stb sk)) *)
(*   → refines2 [MWCImp.MW] [MWC9.MW (global_stb)]. *)
(*   admit "". *)
(*   Qed. *)

  Let CSL0: gname -> bool := fun g => in_dec dec g ["gv0"; "gv1"].
  Let MWLow: refines2 [Mem0.Mem (fun _ => false); MWCImp.MW] [Mem0.Mem CSL0; MWC0.MW].
  Proof.
    transitivity (KMod.transl_tgt_list [KMem CSL0 CSL0; MWC9.KMW]).
    { eapply refines2_cons.
      { eapply Mem0Openproof.correct. ii; ss. }
      { eapply MWCImp9proof.correct.
        i.
        ii. unfold to_closed_stb.
        autounfold with stb in *. autorewrite with stb in *. cbn in *.
        rewrite ! eq_rel_dec_correct in *. des_ifs.
      }
    }
    etrans.
    { eapply adequacy_open. i. exists ε. split.
      { g_wf_tac.
        { Local Transparent Sk.load_skenv _points_to string_dec.
          (* Eval compute in (KMod.get_sk [KMem CSL0 CSL0; KMW]). *)
          replace (KMod.get_sk [KMem CSL0 CSL0; KMW]) with
                  [("get", Sk.Gfun); ("gv0", Sk.Gvar 0); ("gv1", Sk.Gvar 0); ("gv2", Sk.Gvar 0);
                   ("gv3", Sk.Gvar 0); ("loop", Sk.Gfun); ("put", Sk.Gfun)] in * by refl.
          dup SKINCL. dup SKWF.
          eapply Sk.incl_incl_env in SKINCL. eapply Sk.load_skenv_wf in SKWF.
          hexploit (SKINCL "gv0"). { ss. eauto. } intros [blk0 FIND0].
          hexploit (SKINCL "gv1"). { ss. eauto. } intros [blk1 FIND1].
          ur. unfold var_points_to. des_ifs. des; clarify.
          rewrite URA.unit_idl. unfold points_to, Auth.white in *.
          Opaque _points_to SkEnv.id2blk. clarify.
          esplits.
          - r. exists ε.
            extensionality b. extensionality ofs.
            unfold initial_mem_mr.
            des_ifs.
            { assert(s <> "gv0").
              { ii; clarify.
                exploit (SKINCL0 "gv0"); ss; et. intro T.
                eapply nth_error_In in Heq.
                r in SKWF0. ss.
                eapply NoDup_inj_aux; [eassumption| |apply Heq|apply T|..]; ss.
              }
              assert(s <> "gv1").
              { ii; clarify.
                exploit (SKINCL0 "gv1"); ss; et. intro T.
                eapply nth_error_In in Heq.
                r in SKWF0. ss.
                eapply NoDup_inj_aux; [eassumption| |apply Heq|apply T|..]; ss.
              }
              assert(SkEnv.id2blk (Sk.load_skenv sk) s = Some b).
              { Local Transparent SkEnv.id2blk.
                clear - Heq. cbn. uo. des_ifs.
                - admit "somehow?".
                - admit "somehow?".
              }
              assert(b <> blk0).
              { ii. clarify. admit "somehow?". }
              assert(b <> blk1).
              { ii. clarify. admit "somehow?". }
              admit "somehow?".
            }
            { admit "???". }
            { admit "???". }
            { admit "???". }
            { admit "???". }
          - { admit "???". }
        }
      }
      ii. ss. clarify. ss. esplits; ss; et.
      - rr. uipropall.
      - ii. rr in POST. uipropall.
    }
    eapply refines2_cons.
    { eapply MemOpen0proof.correct. }
    { eapply MWC90proof.correct. }
  Qed.

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
