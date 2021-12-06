Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Import ModSemL.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import SimSTS.
Require Import HoareDef.
Require Import SimModSem2.
Require Import HTacticsNoIndex.
From Ordinal Require Import Ordinal Arithmetic.

Set Implicit Arguments.


Module TAC.
  Ltac my_steps := repeat (_steps; des_ifs_safe).
  Ltac my_force_l := _force_l.
  Ltac my_force_r := _force_r.
End TAC.
Import TAC.

Section CANCEL.

  (*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
  Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)



  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.

  Let sk: Sk.t := Sk.sort (fold_right Sk.add Sk.unit (List.map SMod.sk mds)).
  (* Let skenv: SkEnv.t := Sk.load_skenv sk. *)
  Let mss: list SModSem.t := (List.map ((flip SMod.get_modsem) sk) mds).
  Let sbtb: list (gname * fspecbody) := (List.flat_map (SModSem.fnsems) mss).
  Let _stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb.

  Variable stb: gname -> option fspec.
  Hypothesis STBCOMPLETE:
    forall fn fsp (FIND: alist_find fn _stb = Some fsp), stb fn = Some fsp.
  Hypothesis STBSOUND:
    forall fn (FIND: alist_find fn _stb = None),
      (<<NONE: stb fn = None>>) \/ (exists fsp, <<FIND: stb fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>).


  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Let mds_mid2: list Mod.t := List.map (SMod.to_mid2 stb) mds.



  Let W: Type := p_state.

  Opaque EventsL.interp_Es.

  Let ms_src: ModSemL.t := ModL.enclose (Mod.add_list mds_src).
  Let ms_mid2: ModSemL.t := ModL.enclose (Mod.add_list mds_mid2).

  Let p_src := ModSemL.prog ms_src.
  Let p_mid2 := ModSemL.prog ms_mid2.

  Require Import IRed.


  Lemma my_lemma__APC o (w: unit) st
    :
      paco8 (_sim_itree (fun (_: unit) '(st_src, st_tgt) => st_src = st_tgt) top2) bot8 unit unit
            (fun st_src st_tgt _ _ => st_src = st_tgt)
            false false w
            (st, Ret tt)
            (st, interp_hCallE_mid2 (_APC o)).
  Proof.
    ginit. revert w st.
    induction (Ord.lt_well_founded o); i. clear H. rename x into o. rename H0 into IH.
    rewrite unfold_APC. my_steps.
    destruct x.
    { my_steps. }
    my_steps. deflag.
    eapply IH; auto.
  Qed.

  Lemma idK_spec2: forall E A B (a: A) (itr: itree E B), itr = Ret a >>= fun _ => itr. Proof. { i. ired. ss. } Qed.

  Context {CONF: EMSConfig}.
  Theorem adequacy_type_m2s:
    Beh.of_program (ModL.compile (Mod.add_list mds_mid2)) <1=
    Beh.of_program (ModL.compile (Mod.add_list mds_src)).
  Proof.
    eapply ModSem.refines_close.
    eapply (@adequacy_local_list_strong mds_src mds_mid2).
    unfold mds_src, mds_mid2.
    eapply Forall2_apply_Forall2.
    { refl. }
    i. subst. econs; ss. i. econs; ss.
    { instantiate (1:=fun (_ _: unit) => True). ss. }
    { instantiate (1:=fun _ '(st_src, st_tgt) => st_src = st_tgt).
      eapply Forall2_apply_Forall2.
      { refl. }
      i. subst. destruct b0. econs; ss. ii. subst.
      unfold fun_to_src, fun_to_mid2, body_to_src, body_to_mid2. ss.
      generalize (fsb_body f y).
      revert mrs_tgt w. ginit. gcofix CIH. i. ides i.
      { steps. }
      { steps. deflag. gbase. eapply CIH. }
      rewrite <- bind_trigger.
      destruct e.
      { resub. destruct h. ired_both.
        Local Transparent APC. unfold APC. Local Opaque APC.
        force_r. i. ired_both.
        steps. deflag. rewrite (idK_spec2 tt (interp_hEs_src (k ()))).
        guclo lbindC_spec. econs.
        { deflag. gfinal. right. eapply paco8_mon.
          { eapply my_lemma__APC. }
          { i. ss. }
        }
        { i. ss. clear _GUARANTEE. steps. destruct vret_tgt.
          deflag. gbase. et.
        }
      }
      destruct e.
      { resub. destruct c. steps.
        deflag. gbase. et.
      }
      destruct s0.
      { resub. destruct p.
        { ired_both. force_r. force_l. steps.
          deflag. gbase. et.
        }
        { ired_both. force_r. force_l. steps.
          deflag. gbase. et.
        }
      }
      { resub. destruct e.
        { ired_both. force_r. i. force_l. exists x. steps.
          deflag. gbase. et.
        }
        { ired_both. force_l. i. force_r. exists x. steps.
          deflag. gbase. et.
        }
        { ired_both. steps.
          deflag. gbase. et.
        }
      }
    }
    { exists tt. ss. }
    Unshelve. all: ss. 
  Qed.

End CANCEL.
