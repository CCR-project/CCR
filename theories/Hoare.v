Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Export HoareDef.
Require Import Hoareproof0 Hoareproof1.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section AUX________REMOVEME_____REDUNDANT.

  Context `{Σ: GRA.t}.

  Definition refines_closed (md_tgt md_src: ModL.t): Prop :=
    Beh.of_program (ModL.compile md_tgt) <1= Beh.of_program (ModL.compile md_src)
  .

  Global Program Instance refines_closed_PreOrder: PreOrder refines_closed.
  Next Obligation. ii; ss. Qed.
  Next Obligation. ii; ss. r in H. r in H0. eauto. Qed.

End AUX________REMOVEME_____REDUNDANT.



Section CANCEL.

  Context `{Σ: GRA.t}.

  Variable md_tgt: ModL.t.
  Let ms_tgt: ModSemL.t := (ModL.get_modsem md_tgt (Sk.load_skenv md_tgt.(ModL.sk))).

  Variable sbtb: list (gname * fspecbody).
  Let stb: list (gname * fspec) := List.map (fun '(gn, fsb) => (gn, fsb_fspec fsb)) sbtb.

  Let md_mid: ModL.t := md_mid md_tgt sbtb.
  Let ms_mid: ModSemL.t := ms_mid md_tgt sbtb.

  Let md_src: ModL.t := md_src md_tgt sbtb.
  Let ms_src: ModSemL.t := ms_src md_tgt sbtb.

  Let rsum: r_state -> Σ :=
    fun '(mrs_tgt, frs_tgt) => (URA.add (fold_left URA.add (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε)
                                        (fold_left URA.add frs_tgt ε)).

  Hypothesis WTY: ms_tgt.(ModSemL.fnsems) = List.map (fun '(fn, sb) => (fn, (transl_all sb.(fsb_fspec).(mn)) <*> fun_to_tgt stb fn sb)) sbtb.
  Hypothesis WF1: Forall (fun '(_, sp) => In sp.(mn) (List.map fst ms_tgt.(ModSemL.initial_mrs))) stb.
  Variable entry_r: Σ.
  Variable main_pre: Any.t -> ord -> Σ -> Prop.
  Hypothesis MAIN: List.find (fun '(_fn, _) => dec "main" _fn) stb =
                   Some ("main", (mk_simple "Main" (fun (_: unit) => (main_pre, top2)))).
  Hypothesis MAINPRE: main_pre ([]: list val)↑ ord_top entry_r.
  Hypothesis WFR: URA.wf (entry_r ⋅ rsum (ModSemL.initial_r_state ms_tgt)).

  Theorem adequacy_type: refines_closed md_tgt md_src.
  Proof.
    ii. eapply adequacy_type_m2s. eapply adequacy_type_t2m; et.
  Qed.

End CANCEL.




Section AUX.

  Context `{Σ: GRA.t}.

  Lemma modl_eta: forall x0 x1 y0 y1, x0 = x1 -> y0 = y1 -> (ModL.mk x0 y0) = (ModL.mk x1 y1).
  Proof. i; subst. refl. Qed.

  Lemma modseml_eta: forall x0 x1 y0 y1, x0 = x1 -> y0 = y1 -> (ModSemL.mk x0 y0) = (ModSemL.mk x1 y1).
  Proof. i; subst. refl. Qed.

End AUX.


Lemma sk_unit_id: forall sk, (Sk.add sk Sk.unit) = sk.
Proof. i. unfold Sk.add, Sk.unit. rewrite app_nil_r. refl. Qed.

Lemma sk_unit_idl: forall sk, (Sk.add Sk.unit sk) = sk.
Proof. i. unfold Sk.add, Sk.unit. rewrite app_nil_l. refl. Qed.






Section BETTER.

  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.

  Let sk: Sk.t := fold_right Sk.add Sk.unit (List.map SMod.sk mds).
  Let skenv: SkEnv.t := Sk.load_skenv sk.
  Let mss: list SModSem.t := (List.map ((flip SMod.get_modsem) skenv) mds).
  (* Let stb: list (gname * fspec) := List.concat (List.map (List.map (fun '(fn, fs) => (fn, fsb_fspec fs)) ∘ SModSem.fnsems) mss). *)
  Let sbtb: list (gname * fspecbody) := (List.flat_map (SModSem.fnsems) mss).
  (* Let stb: list (gname * fspec) := (List.flat_map (List.map (fun '(fn, fs) => (fn, fsb_fspec fs)) ∘ SModSem.fnsems) mss). *)
  Let stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb.

  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Let mds_tgt: list Mod.t := List.map (SMod.to_tgt stb) mds.

  (* Let rsum: r_state -> Σ := *)
  (*   fun '(mrs_tgt, frs_tgt) => (URA.add (fold_left URA.add (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε) *)
  (*                                       (fold_left URA.add frs_tgt ε)). *)

  Variable entry_r: Σ.
  Variable main_pre: Any.t -> ord -> Σ -> Prop.
  Hypothesis MAIN: List.find (fun '(_fn, _) => dec "main" _fn) stb =
                   Some ("main", (mk_simple "Main" (fun (_: unit) => (main_pre, top2)))).
  Hypothesis MAINPRE: main_pre ([]: list val)↑ ord_top entry_r.
  (* Hypothesis WFR: URA.wf (entry_r ⋅ fold_right (⋅) ε (List.map SModSem.initial_mr mss)). *)
  Hypothesis WFR: URA.wf (entry_r ⋅ fold_left (⋅) (List.map SModSem.initial_mr mss) ε).

  Theorem adequacy_type_better: refines_closed (Mod.add_list mds_tgt) (Mod.add_list mds_src).
  Proof.
    etrans.
    { eapply adequacy_type; et.
      - unfold mds_tgt. ss.
        replace (Sk.load_skenv (ModL.sk (Mod.add_list (List.map (SMod.to_tgt stb) mds)))) with skenv; cycle 1.
        { unfold skenv. f_equal. unfold sk. unfold Mod.add_list.
          rewrite List.map_map. clear.
          (* subst_locals. *)
          induction mds; ii; ss.
          rewrite IHl.
          assert(U: forall x y z, x = y -> Sk.add z x = Sk.add z y).
          { i; subst; refl. }
          eapply U.
          assert(V: forall x y, x = y -> ModL.sk x = ModL.sk y).
          { i; subst; refl. }
          eapply V.
          assert(W: forall A B (s: A) (f: B -> A -> A) x y, x = y -> fold_right f s x = fold_right f s y).
          { i; subst; refl. }
          eapply W.
          eapply map_ext. i. r.
          replace (List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec)))
                            (flat_map SModSem.fnsems (List.map (flip SMod.get_modsem
                                      (Sk.load_skenv (fold_right Sk.add Sk.unit (List.map SMod.sk l)))) l))) with stb.
          { refl. }
          unfold stb. unfold sbtb.
          clear.
          rewrite ! flat_map_concat_map.
          rewrite concat_map.
          eapply map_ext.
          f_equal.
          (* Set Ltac Profiling. Show Ltac Profile. *)
          f_equal.
          destruct mds; ss. clear mds.
          destruct l; ss.
          destruct l; ss.
          destruct l; ss.
          {
          admit "somehow".
        }
        unfold Mod.add_list. unfold Mod.lift.
        admit "somehow?".
      - des_ifs. ss. erewrite f_equal; [apply WFR|]. repeat f_equal.
        unfold ModSemL.initial_r_state in Heq. clarify. ss. repeat rewrite URA.unit_id. f_equal.
        admit "somehow?".
    }
    erewrite f_equal.
    { refl. }
    unfold md_src, mds_src.
    clear. subst_locals.
    destruct mds; ss.
    destruct l; ss.
    { rewrite List.app_nil_r. rewrite ! Mod.add_list_single.
      destruct t; ss. cbn. unfold SMod.to_src. ss.
      eapply modl_eta; ss; cycle 1.
      { admit "". }
      apply func_ext. i. unfold ms_src. ss.
      assert(x = Sk.load_skenv sk) by admit "". subst.
      unfold SModSem.to_src. eapply modseml_eta; ss; cycle 1.
      unfold ModSem.map_snd. unfold compose.
      rewrite sk_unit_id.
      set (skenv:=(Sk.load_skenv sk)).
      rewrite List.map_map. f_equal.
      apply func_ext. i. des_ifs. f_equal.
      assert(T: mn f = (SModSem.mn (get_modsem skenv))).
      { admit "mn condition". }
      rewrite T. refl.
    }
    admit "".
  Qed.

End BETTER.
