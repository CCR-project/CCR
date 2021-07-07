Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import HoareDef Hoare.
Require Import OpenDef.
Require Import IRed.
Require Import SimModSem.

Set Implicit Arguments.





Global Program Instance Forall2_Reflexive `{Reflexive A R}: Reflexive (Forall2 R).
Next Obligation. induction x; ii; ss. econs; ss. Qed.

Global Program Instance Forall2_Transitive `{Transitive A R}: Transitive (Forall2 R).
Next Obligation.
  i. revert_until x. induction x; ii; ss.
  { inv H0. inv H1. ss. }
  inv H0. inv H1. econs; ss; et.
Qed.

Global Program Instance Forall2_PreOrder `{PreOrder A R}: PreOrder (Forall2 R).

Lemma alist_find_map_snd K R `{RD_K: @RelDec K R} A B (f: A -> B) (l: alist K A) k
  :
    alist_find k (map (map_snd f) l)
    =
    o_map (alist_find k l) f.
Proof.
  induction l; ss. destruct a. ss. uo. des_ifs.
Qed.

(*** TODO: move ***)
Section ITREEAUX.
  Definition trivial_state_Handler `{E -< F} {S}: E ~> (stateT S (itree F)) :=
    fun T X s => x <- trigger X;; Ret (s, x).

  Definition addtau `{eventE -< E}: itree E ~> itree E := interp (fun _ (e: E _) => tau;; trigger e).

  Definition addtau_ktr `{eventE -< E} {R}: ktree E R ~> ktree E R := fun _ ktr => addtau(T:=_) ∘ ktr.

  Section ADDTAU.
  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)
  Context `{eventE -< E}.

  Lemma addtau_bind
        (R S: Type)
        (s: itree E R) (k : R -> itree E S)
    :
      (addtau (s >>= k))
      =
      ((addtau (E:=E) s) >>= (fun r => addtau (k r))).
  Proof.
    unfold addtau in *. grind.
  Qed.

  Lemma addtau_tau
        (U: Type)
        (t : itree _ U)
    :
      (addtau (E:=E) (Tau t))
      =
      (Tau (addtau t)).
  Proof.
    unfold addtau in *. grind.
  Qed.

  Lemma addtau_ret
        (U: Type)
        (t: U)
    :
      ((addtau (E:=E) (Ret t)))
      =
      Ret t.
  Proof.
    unfold addtau in *. grind.
  Qed.

  Lemma addtau_event
        (R: Type)
        (i: E R)
    :
      (addtau (E:=E) (trigger i))
      =
      tau;; (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold addtau in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma addtau_triggerUB
        (R: Type)
    :
      (addtau (E:=E) (triggerUB))
      =
      tau;; triggerUB (A:=R).
  Proof.
    unfold addtau, triggerUB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma addtau_triggerNB
        (R: Type)
    :
      (addtau (E:=E) (triggerNB))
      =
      tau;; triggerNB (A:=R).
  Proof.
    unfold addtau, triggerNB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma addtau_unwrapU
        (R: Type)
        (i: option R)
    :
      (addtau (E:=E) (unwrapU i))
      =
      match i with
      | Some r => Ret r
      | _ => tau;; triggerUB
      end.
  Proof.
    unfold addtau. unfold unwrapU. des_ifs; grind. eapply addtau_triggerUB.
  Qed.

  Lemma addtau_unwrapN
        (R: Type)
        (i: option R)
    :
      (addtau (E:=E) (unwrapN i))
      =
      match i with
      | Some r => Ret r
      | _ => tau;; triggerNB
      end.
  Proof.
    unfold addtau. unfold unwrapN. des_ifs; grind. eapply addtau_triggerNB.
  Qed.

  Lemma addtau_assume
        P
    :
      (addtau (E:=E) (assume P))
      =
      (tau;; assume P;;; tau;; Ret tt)
  .
  Proof.
    unfold addtau, assume. grind. rewrite unfold_interp; cbn. grind.
  Qed.

  Lemma addtau_guarantee
        P
    :
      (addtau (E:=E) (guarantee P))
      =
      (tau;; guarantee P;;; tau;; Ret tt).
  Proof.
    unfold addtau, guarantee. grind. rewrite unfold_interp; cbn. grind.
  Qed.

  Lemma addtau_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (addtau (E:=E) itr0)
      =
      (addtau itr1)
  .
  Proof. subst; et. Qed.

  Global Program Instance addtau_rdb: red_database (mk_box (@addtau E H)) :=
    mk_rdb
      0
      (mk_box addtau_bind)
      (mk_box addtau_tau)
      (mk_box addtau_ret)
      (mk_box addtau_event)
      (mk_box True)
      (mk_box True)
      (mk_box True)
      (mk_box addtau_triggerUB)
      (mk_box addtau_triggerNB)
      (mk_box addtau_unwrapU)
      (mk_box addtau_unwrapN)
      (mk_box addtau_assume)
      (mk_box addtau_guarantee)
      (mk_box addtau_ext)
  .
  Global Opaque addtau.
End ADDTAU.
End ITREEAUX.
Goal forall `{eventE -< E} X, (addtau (E:=E) (T:=X) triggerUB) = tau;; triggerUB.
Proof. i. my_red_both. refl. Qed.



Module AUX.
  Ltac ord_tac := eapply OrdArith.lt_from_nat; eapply Nat.lt_succ_diag_r.
End AUX.
Import AUX.
Section MODAUX.
  Context {CONF: EMSConfig}.
  Context `{Σ: GRA.t}.

  Definition addtau_ms (ms: ModSem.t): ModSem.t := {|
    ModSem.fnsems := map (map_snd (addtau_ktr(T:=_))) ms.(ModSem.fnsems);
    ModSem.mn := ms.(ModSem.mn);
    ModSem.initial_st := ms.(ModSem.initial_st);
  |}
  .

  Definition addtau_md (md: Mod.t): Mod.t := {|
    Mod.get_modsem := addtau_ms ∘ md.(Mod.get_modsem);
    Mod.sk := md.(Mod.sk);
  |}
  .

  Theorem adequacy_addtau
          (md: Mod.t)
    :
      ModPair.sim (addtau_md md) md
  .
  Proof.
    econs; ss. i. econs.
    { instantiate (1:=fun (_ _: unit) => True). ss. }
    { instantiate (1:=fun (_: unit) '(st_src, st_tgt) => st_src = st_tgt). ss.
      rewrite <- map_id. eapply Forall2_fmap_2. eapply Forall2_impl.
      { refl. }
      i. subst. destruct y as [fn f]. econs; ss. ii. subst. ss. exists 10.
      unfold addtau_ktr.
      generalize (f y). revert w mrs_tgt.
      pcofix CIH. i. ides i.
      { pfold. rewrite addtau_ret. econs; et. red. esplits; et. }
      { pfold. rewrite addtau_tau. econs; et. }
      { rewrite <- bind_trigger. resub.
        rewrite addtau_bind. rewrite addtau_event.
        rewrite bind_tau. rewrite bind_bind.
        pfold. econs; [ord_tac|].
        left. destruct e.
        { destruct c. resub. pfold. econs; et. i. subst.
          esplits. left. rewrite bind_tau. pfold. econs; [ord_tac|].
          right. rewrite bind_ret_l. eapply CIH.
        }
        destruct s.
        { resub. destruct p.
          { pfold. econs; et. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
          { pfold. econs; et. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
        }
        { resub. destruct e.
          { pfold. econs; et. i. esplits. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
          { pfold. econs; et. i. esplits. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
          { pfold. econs; et. i. esplits. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
        }
      }
    }
    { ss. }
    { exists tt. ss. }
  Qed.

  Theorem adequacy_rmtau
          md
    :
      ModPair.sim md (addtau_md md)
  .
  Proof.
    econs; ss. i. econs.
    { instantiate (1:=fun (_ _: unit) => True). ss. }
    { instantiate (1:=fun (_: unit) '(st_src, st_tgt) => st_src = st_tgt). ss.
      erewrite <- map_id at 1. eapply Forall2_fmap_2. eapply Forall2_impl.
      { refl. }
      i. subst. destruct y as [fn f]. econs; ss. ii. subst. ss. exists 10.
      unfold addtau_ktr.
      generalize (f y). revert w mrs_tgt.
      pcofix CIH. i. ides i.
      { pfold. rewrite addtau_ret. econs; et. red. esplits; et. }
      { pfold. rewrite addtau_tau. econs; et. }
      { rewrite <- bind_trigger. resub.
        rewrite addtau_bind. rewrite addtau_event.
        rewrite bind_tau. rewrite bind_bind.
        pfold. econs; [ord_tac|].
        left. destruct e.
        { destruct c. resub. pfold. econs; et. i. subst.
          esplits. left. rewrite bind_tau. pfold. econs; [ord_tac|].
          right. rewrite bind_ret_l. eapply CIH.
        }
        destruct s.
        { resub. destruct p.
          { pfold. econs; et. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
          { pfold. econs; et. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
        }
        { resub. destruct e.
          { pfold. econs; et. i. esplits. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
          { pfold. econs; et. i. esplits. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
          { pfold. econs; et. i. esplits. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
        }
      }
    }
    { ss. }
    { exists tt. ss. }
  Qed.
End MODAUX.





Module Massage.
Section MASSAGE.
  Context {CONF: EMSConfig}.
  Context `{Σ: GRA.t}.
  (* Variant frE: Type -> Type := *)
  (* | FPut' (fr0: Σ): frE unit *)
  (* | FGet': frE Σ *)
  (* . *)
  Definition massage_callE (b: bool): callE ~> itree hEs :=
    if b
    then
      fun T '(Call fn args) => trigger (Call fn (Any.pair false↑ args))
    else
      fun T '(Call fn args) => trigger (Call fn args)
  .

  Definition massage_itr b: itree Es ~> itree hEs :=
    (* interp (case_ (massage_callE) (case_ (massage_rE) (case_ (massage_pE) trivial_state_Handler))) *)
    interp (case_ (massage_callE b) trivial_Handler)
  .

  Definition massage_fun (b: bool) (ktr: (option mname * Any.t) -> itree Es Any.t): ((option mname * Any.t) -> itree hEs Any.t) :=
    if b
    then
      fun '(mn, args) =>
        '(_, args) <- (Any.split args)ǃ;;
        massage_itr b (ktr (mn, args))
    else
      fun '(mn, args) =>
        massage_itr b (ktr (mn, args))
  .

  Definition massage_fsb b: ((option mname * Any.t) -> itree Es Any.t) -> fspecbody :=
    fun ktr => mk_specbody (KModSem.disclose_mid fspec_trivial) (massage_fun b ktr)
  .

  Definition massage_ms b (ms: ModSem.t): SModSem.t := {|
    SModSem.fnsems := List.map (map_snd (massage_fsb b)) ms.(ModSem.fnsems);
    SModSem.mn := ms.(ModSem.mn);
    SModSem.initial_mr := ε;
    SModSem.initial_st := ms.(ModSem.initial_st);
                                                      |}
  .


  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)
  Lemma massage_itr_bind b
        (R S: Type)
        (s: itree _ R) (k : R -> itree _ S)
    :
      (massage_itr b (s >>= k))
      =
      ((massage_itr b s) >>= (fun r => massage_itr b (k r))).
  Proof.
    unfold massage_itr in *. rewrite interp_bind. grind.
  Qed.

  Lemma massage_itr_tau b
        (U: Type)
        (t : itree _ U)
    :
      (massage_itr b (tau;; t))
      =
      (tau;; (massage_itr b t)).
  Proof.
    unfold massage_itr in *. rewrite interp_tau. grind.
  Qed.

  Lemma massage_itr_ret b
        (U: Type)
        (t: U)
    :
      ((massage_itr b (Ret t)))
      =
      Ret t.
  Proof.
    unfold massage_itr in *. rewrite interp_ret. grind.
  Qed.

  Lemma massage_itr_pe b
        (R: Type)
        (i: pE R)
    :
      (massage_itr b (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold massage_itr in *. rewrite interp_trigger. grind.
  Qed.

  Lemma massage_itr_calle b
        (R: Type)
        (i: callE R)
    :
      (massage_itr b (trigger i))
      =
      ((massage_callE b i) >>= (fun r => tau;; Ret r)).
  Proof.
    unfold massage_itr in *. rewrite interp_trigger. grind.
  Qed.

  Lemma massage_itr_evente b
        (R: Type)
        (i: eventE R)
    :
      (massage_itr b (trigger i))
      =
      ((trigger i) >>= (fun r => tau;; Ret (r))).
  Proof.
    unfold massage_itr in *. rewrite interp_trigger. grind.
  Qed.

  Lemma massage_itr_triggerUB b
        (R: Type)
    :
      (massage_itr b (triggerUB))
      =
      triggerUB (A:=R).
  Proof.
    unfold massage_itr, triggerUB in *. rewrite unfold_interp. cbn.
    unfold trivial_state_Handler. grind.
  Qed.

  Lemma massage_itr_triggerNB b
        (R: Type)
    :
      (massage_itr b (triggerNB))
      =
      triggerNB (A:=(R)).
  Proof.
    unfold massage_itr, triggerNB in *. rewrite unfold_interp. cbn.
    unfold trivial_state_Handler. grind.
  Qed.

  Lemma massage_itr_unwrapU b
        (R: Type)
        (i: option R)
    :
      (massage_itr b (unwrapU i))
      =
      unwrapU i.
  Proof.
    unfold massage_itr, unwrapU in *. des_ifs.
    { etrans.
      { eapply massage_itr_ret. }
      { grind. }
    }
    { etrans.
      { eapply massage_itr_triggerUB. }
      { unfold triggerUB. grind. }
    }
  Qed.

  Lemma massage_itr_unwrapN b
        (R: Type)
        (i: option R)
    :
      (massage_itr b (unwrapN i))
      =
      unwrapN i.
  Proof.
    unfold massage_itr, unwrapN in *. des_ifs.
    { etrans.
      { eapply massage_itr_ret. }
      { grind. }
    }
    { etrans.
      { eapply massage_itr_triggerNB. }
      { unfold triggerNB. grind. }
    }
  Qed.

  Lemma massage_itr_assume b
        P
    :
      (massage_itr b (assume P))
      =
      (assume P;;; tau;; Ret (tt))
  .
  Proof.
    unfold assume. rewrite massage_itr_bind. rewrite massage_itr_evente. grind. eapply massage_itr_ret.
  Qed.

  Lemma massage_itr_guarantee b
        P
    :
      (massage_itr b (guarantee P))
      =
      (guarantee P;;; tau;; Ret (tt)).
  Proof.
    unfold guarantee. rewrite massage_itr_bind. rewrite massage_itr_evente. grind. eapply massage_itr_ret.
  Qed.

  Lemma massage_itr_ext b
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (massage_itr b itr0)
      =
      (massage_itr b itr1)
  .
  Proof. subst; et. Qed.
End MASSAGE.
End Massage.
Import Massage.


Section RDB.
  Context `{Σ: GRA.t}.
  Definition massage_md b (md: Mod.t): SMod.t := {|
    SMod.get_modsem := fun sk => massage_ms b (Mod.get_modsem md sk);
    SMod.sk := md.(Mod.sk);
  |}
  .
  Global Program Instance transl_itr_rdb: red_database (mk_box (@massage_itr)) :=
    mk_rdb
      0
      (mk_box massage_itr_bind)
      (mk_box massage_itr_tau)
      (mk_box massage_itr_ret)
      (mk_box massage_itr_calle)
      (mk_box massage_itr_pe)
      (mk_box massage_itr_pe)
      (mk_box massage_itr_evente)
      (mk_box massage_itr_triggerUB)
      (mk_box massage_itr_triggerNB)
      (mk_box massage_itr_unwrapU)
      (mk_box massage_itr_unwrapN)
      (mk_box massage_itr_assume)
      (mk_box massage_itr_guarantee)
      (mk_box massage_itr_ext)
  .
End RDB.




Require Import Hoare.
Require Import HTactics ProofMode.



Section ADQ.
  Context {CONF: EMSConfig}.
  Context `{Σ: GRA.t}.

  Variable _kmds: list KMod.t.
  Let frds: Sk.t -> list mname := KMod.get_frds _kmds.
  Let _gstb: Sk.t -> list (gname * fspec) := KMod.get_stb _kmds.
  Let _stb: Sk.t -> gname -> option fspec :=
    fun sk fn => match alist_find fn (_gstb sk) with
                 | Some fsp => Some (KModSem.disclose_mid fsp)
                 | _ => Some (KModSem.disclose_mid fspec_trivial)
                 end.

  Let kmds: list SMod.t := List.map KMod.transl_mid _kmds.
  Let _kmss: Sk.t -> list SModSem.t := fun ske => List.map (flip SMod.get_modsem ske) kmds.

  Section UMDS.
  Variable umds: list Mod.t.
  Let sk_link: Sk.t := Sk.sort (fold_right Sk.add Sk.unit ((List.map SMod.sk kmds) ++ (List.map Mod.sk umds))).
  Let skenv: SkEnv.t := Sk.load_skenv sk_link.
  Let _umss: Sk.t -> list ModSem.t := fun ske => List.map (flip Mod.get_modsem ske) umds.
  Let kmss: list SModSem.t := Eval red in (_kmss sk_link).
  Let umss: list ModSem.t := Eval red in (_umss sk_link).
  Let gstb: list (gname * fspec) := Eval red in (_gstb sk_link).
  Let _frds: list (option mname) := (None :: (List.map Some (frds sk_link))).

  Hypothesis MNNODUP:
    forall mn
           (MIN0: List.In (Some mn) _frds)
           (MIN1: List.In mn (map (ModSem.mn ∘ flip Mod.get_modsem sk_link) umds)),
      False.

  Lemma add_list_fnsems
        mds ske
    :
      (ModSemL.fnsems (ModL.get_modsem (Mod.add_list mds) ske)) =
      flat_map ModSemL.fnsems (List.map (flip ModL.get_modsem ske ∘ Mod.lift) mds)
  .
  Proof. induction mds; ss. f_equal. et. Qed.
  Ltac _list_tac :=
    match goal with
    | [ H: alist_find _ _ = Some _ |- _ ] => apply alist_find_some in H; des; des_sumbool; subst
    | [ H: context[ModL.enclose] |- _ ] => unfold ModL.enclose in H; try rewrite add_list_fnsems in H
    | [ H: In _ (flat_map _ _) |- _ ] => apply in_flat_map in H; des
    | [ H: In _ (List.map _ _) |- _ ] => apply in_map_iff in H; des
    | [ H: map_snd _ _ = _ |- _ ] => unfold map_snd in H; ss
    | [ H: flip _ _ _ = _ |- _ ] => unfold flip in H; ss
    | [ |- context[ModL.enclose] ] => unfold ModL.enclose; try rewrite add_list_fnsems
    | [ |- In _ (flat_map _ _) ] => apply in_flat_map; esplits; et
    | [ |- In _ (List.map _ _) ] => apply in_map_iff; esplits; et
    | [ |- map_snd _ _ = _ ] => unfold map_snd; ss
    | [ |- flip _ _ _ = _ ] => unfold flip; ss
    end
  .
  Ltac list_tac := repeat _list_tac.

  Lemma my_lemma1_aux''
        (ske: Sk.t) st0 (A: Type) (itr: itree Es A) (ctx: Σ)
        mn
        (* (WF: URA.wf (ctx ⋅ mr0)) *)
        (WF: URA.wf ctx)
    :
      paco7
        (_sim_itree (fun (_: unit) '(st_src, st_tgt) => st_src = Any.pair st_tgt (ε: Σ)↑) top2)
        bot7
        (Σ * A)%type A
        (fun st_src st_tgt '(ctx, r_src) r_tgt =>
           r_src = r_tgt /\ URA.wf ctx /\ st_src = Any.pair st_tgt (ε: Σ)↑)
        40%nat tt
        (Any.pair st0 (ε: Σ)↑, (interp_hCallE_tgt mn (_stb ske) ord_top (interp_hEs_tgt (massage_itr true itr)) ctx))
        (st0, addtau itr)
  .
  Proof.
    ginit. revert_until ske. gcofix CIH. i. ides itr.
    { steps. }
    { rewrite massage_itr_tau. steps. gbase. eapply CIH; et. }
    rewrite <- bind_trigger. rewrite massage_itr_bind. (* TODO: why reduction tactic doesn't work?? *)
    destruct e; cycle 1.
    {
      destruct s; ss.
      { resub. rewrite massage_itr_pe. destruct p; ss.
        - steps. guclo lordC_spec. econs.
          { eapply OrdArith.add_base_l. }
          gbase. eapply CIH; et.
        - steps. guclo lordC_spec. econs.
          { eapply OrdArith.add_base_l. }
          gbase. eapply CIH; et.
      }
      { resub. rewrite massage_itr_evente. destruct e; ss.
        - resub. ired_both. resub.
          gstep. eapply sim_itree_tau_tgt; eauto with ord_step.
          ired_both. gstep; econs; et. i. esplits; et. steps.
          guclo lordC_spec. econs.
          { eapply OrdArith.add_base_l. }
          gbase. eapply CIH; et.
        - resub. ired_both. resub.
          gstep. eapply sim_itree_tau_tgt; eauto with ord_step.
          ired_both. gstep; econs; et. i. esplits; et. steps.
          guclo lordC_spec. econs.
          { eapply OrdArith.add_base_l. }
          gbase. eapply CIH; et.
        - resub. ired_both. resub.
          gstep. eapply sim_itree_tau_tgt; eauto with ord_step.
          ired_both. gstep; econs; et. i. esplits; et. steps.
          guclo lordC_spec. econs.
          { eapply OrdArith.add_base_l. }
          gbase. eapply CIH; et.
      }
    }
    destruct c. resub. rewrite massage_itr_calle. ired_both. resub. steps.
    destruct (_stb ske fn) eqn:STB.
    2: { unfold _stb in *. des_ifs. }
    steps.
    unfold _stb, _gstb in STB. des_ifs.
    - rename Heq into T. eapply alist_find_some in T.
      unfold KMod.get_stb in T. list_tac.
      des_ifs. ss. list_tac. des_ifs. ss.
      Local Transparent HoareCall.
      unfold HoareCall, mput, mget. steps.
      force_l. exists (ε, ε, ε). steps.
      force_l.
      { rewrite ! URA.unit_id. rewrite ! URA.unit_idl. auto. }
      steps. force_l. exists None. steps.
      force_l. exists (args). steps.
      force_l. exists ord_top. steps.
      force_l.
      { split; auto. }
      steps. force_l.
      { split; et. }
      steps. gstep. econs; et.
      { exact tt. }
      i. des_ifs. des; subst. eexists. steps.
      destruct w1.
      guclo lordC_spec. econs.
      { eapply OrdArith.add_base_l. }
      gbase. eapply CIH; et.
      eapply URA.wf_mon; et. instantiate (1:=c). r_wf _ASSUME.
    - unfold HoareCall, mput, mget. steps.
      force_l. exists (ε, ε, ε). steps.
      force_l.
      { rewrite ! URA.unit_id. rewrite ! URA.unit_idl. auto. }
      steps. force_l. exists None. steps.
      force_l. eexists (args). steps.
      force_l. exists ord_top. steps.
      force_l.
      { split; et. }
      steps. force_l.
      { split; et. }
      steps. gstep. econs; et.
      { exact tt. }
      i. des_ifs. des; subst. eexists. steps.
      destruct w1.
      guclo lordC_spec. econs.
      { eapply OrdArith.add_base_l. }
      gbase. eapply CIH; et.
      eapply URA.wf_mon; et. instantiate (1:=c). r_wf _ASSUME.
      Unshelve.
      all: try (exact Ord.O).
      all: try (exact 0%nat).
  Qed.

  Lemma my_lemma1_aux
        mn ske
        ktr arg st0
    :
      sim_itree (fun (_: unit) '(st_src, st_tgt) => st_src = Any.pair st_tgt (ε: Σ)↑) top2 100%nat tt
                ((Any.pair st0 (ε: Σ)↑), fun_to_tgt mn (_stb ske) (massage_fsb true ktr) arg)
                (st0, addtau (ktr arg))
  .
  Proof.
    Local Transparent HoareFun.
    unfold fun_to_tgt, HoareFun, mput, mget, cfunN.
    Local Opaque HoareFun.
    ginit. steps.
    assert (x1 = ord_top /\ exists b, x0 = Any.pair b t).
    { destruct x; ss.
      { des. subst. red in _ASSUME1. uipropall. des. clarify. et. }
      { des. subst. et. }
    }
    des; clarify. clear _ASSUME0.
    unfold massage_fun.
    rewrite Any.pair_split. steps.
    guclo lordC_spec. econs.
    { instantiate (1:=(29 + (40))%ord). rewrite <- ! OrdArith.add_from_nat; cbn. eapply OrdArith.le_from_nat. lia. }
    erewrite idK_spec with (i0:=(addtau (ktr (o, t)))).
    guclo lbindC_spec. econs.
    { instantiate (1:=tt).
      gfinal. right. eapply my_lemma1_aux''; et.
      eapply URA.wf_mon; et. instantiate (1:=c). r_wf _ASSUME.
    }
    i. des_ifs. ss. des_ifs. ss. des; clarify. unfold idK. steps.
    force_l. eexists. force_l. eexists (_, _). steps.
    force_l.
    { instantiate (1:=ε). instantiate (1:=ε). r_wf SIM0. }
    steps. force_l.
    { red. destruct x; et. red. uipropall. }
    steps.
  Qed.

  Lemma my_lemma1
        umd
        (IN: In umd umds)
    :
      ModPair.sim (SMod.to_tgt _stb (massage_md true umd)) (addtau_md umd)
  .
  Proof.
    econs; ss.
    i. r. econs.
    { instantiate (1:=fun (_ _: unit) => True). ss. }
    { instantiate (1:=(fun (_: unit) '(st_src, st_tgt) => st_src = Any.pair st_tgt (ε: Σ)↑)). ss.
      set (ums:=Mod.get_modsem umd sk) in *.
      rewrite ! List.map_map.
      eapply Forall2_apply_Forall2.
      { refl. }
      i. subst. unfold map_snd. des_ifs.
      rr. split; ss. r. ii. destruct w. des_ifs. des; subst. ss. esplits; et. eapply my_lemma1_aux.
    }
    { ss. }
    { ss. }
  Qed.

  Require Import SimGlobal.

  Let prog_src := Mod.add_list (map (KMod.transl_src frds) _kmds ++ umds).
  Let prog_mid := Mod.add_list (map (KMod.transl_src frds) _kmds ++ map (SMod.to_src ∘ massage_md false) umds).
  Let prog_tgt := Mod.add_list (map SMod.to_src kmds ++ map (SMod.to_src ∘ massage_md true) umds).

  Lemma option_rel_impl A B (R0 R1: A -> B -> Prop)
        (LE: R0 <2= R1)
    :
      option_rel R0 <2= option_rel R1.
  Proof.
    i. inv PR; et.
  Qed.

  Let stb_find_iff_mid_kmd sk fn:
    option_rel
      (fun f0 f1 =>
         exists mn ksb,
           f0 = transl_all (T:=_) mn ∘ KModSem.disclose_ksb_src (frds sk) ksb /\
           f1 = transl_all (T:=_) mn ∘ (fun_to_src (KModSem.disclose_ksb_mid ksb).(fsb_body)) /\
           List.In mn (frds sk))
      (alist_find
         fn
         (ModSemL.fnsems
            (ModL.get_modsem (Mod.add_list (map (KMod.transl_src frds) _kmds)) sk)))
      (alist_find
         fn
         (ModSemL.fnsems
            (ModL.get_modsem
               (Mod.add_list (map SMod.to_src (map KMod.transl_mid _kmds))) sk))).
  Proof.
    unfold frds at 2. generalize frds. i.
    rewrite ! add_list_fnsems. rewrite ! map_map. rewrite ! flat_map_map. ss.
    generalize _kmds. i. revert fn. induction _kmds0; ss.
    i. ss. rewrite ! alist_find_app_o.
    rewrite ! alist_find_map_snd. uo.
    change (fun '(fn0, sb) => (fn0: string, fun_to_src (fsb_body sb)))
      with (map_snd (A:=string) (fun_to_src ∘ fsb_body)).
    rewrite ! alist_find_map_snd. uo. des_ifs.
    { econs. esplits; et. }
    { eapply option_rel_impl; [|eapply IH_kmds0].
      i. ss. des. esplits; et. }
  Qed.

  Let stb_find_iff_mid_umd sk fn:
    option_rel
      (fun f0 f1 =>
         exists mn uf,
           f0 = transl_all (T:=_) mn ∘ (fun_to_src (massage_fsb false uf).(fsb_body)) /\
           f1 = transl_all (T:=_) mn ∘ (fun_to_src (massage_fsb true uf).(fsb_body)) /\
           List.In mn (map (ModSem.mn ∘ flip Mod.get_modsem sk) umds))
      (alist_find
         fn
         (ModSemL.fnsems
            (ModL.get_modsem (Mod.add_list (map (SMod.to_src ∘ massage_md false) umds)) sk)))
      (alist_find
         fn
         (ModSemL.fnsems
            (ModL.get_modsem
               (Mod.add_list (map (SMod.to_src ∘ massage_md true) umds)) sk))).
  Proof.
    rewrite ! add_list_fnsems. rewrite ! map_map. rewrite ! flat_map_map. ss.
    generalize umds. i. revert fn. induction umds0; ss.
    i. ss. rewrite ! alist_find_app_o.
    rewrite ! alist_find_map_snd. uo.
    change (fun '(fn0, sb) => (fn0: string, fun_to_src (fsb_body sb)))
      with (map_snd (A:=string) (fun_to_src ∘ fsb_body)).
    rewrite ! alist_find_map_snd. uo. des_ifs.
    { econs. esplits; et. }
    { eapply option_rel_impl; [|eapply IHumds0].
      i. ss. des. esplits; et. }
  Qed.

  Lemma stb_find_iff_mid fn
    :
      ((<<SRC: alist_find fn (ModSemL.fnsems (ModL.enclose prog_mid)) = None>>) /\
       (<<TGT: alist_find fn (ModSemL.fnsems (ModL.enclose prog_tgt)) = None>>)) \/
      (exists mn ksb,
          (<<SRC: alist_find fn (ModSemL.fnsems (ModL.enclose prog_mid)) = Some (transl_all (T:=_) mn ∘ KModSem.disclose_ksb_src (frds sk_link) ksb)>>) /\
          (<<TGT: alist_find fn (ModSemL.fnsems (ModL.enclose prog_tgt)) = Some (transl_all (T:=_) mn ∘ (fun_to_src (KModSem.disclose_ksb_mid ksb).(fsb_body)))>>) /\
          (<<MN: List.In (Some mn) _frds>>)) \/
      (exists mn uf,
          (<<SRC: alist_find fn (ModSemL.fnsems (ModL.enclose prog_mid)) = Some (transl_all (T:=_) mn ∘ (fun_to_src (massage_fsb false uf).(fsb_body)))>>) /\
          (<<TGT: alist_find fn (ModSemL.fnsems (ModL.enclose prog_tgt)) = Some (transl_all (T:=_) mn ∘ (fun_to_src (massage_fsb true uf).(fsb_body)))>>) /\
          (<<MN: ~ List.In (Some mn) _frds>>)).
  Proof.
    unfold ModL.enclose, prog_mid, prog_tgt, kmds. ss.
    replace (Sk.sort
               (ModL.sk
                  (Mod.add_list
                     (map (KMod.transl_src frds) _kmds ++
                          map (SMod.to_src ∘ massage_md false) umds)))) with sk_link.
    2: { unfold sk_link, kmds. f_equal. rewrite ! Mod.add_list_sk. f_equal.
         rewrite ! map_app. rewrite ! map_map. ss. }
    replace (Sk.sort
               (ModL.sk
                  (Mod.add_list
                     (map SMod.to_src (map KMod.transl_mid _kmds) ++
                          map (SMod.to_src ∘ massage_md true) umds)))) with sk_link.
    2: { unfold sk_link, kmds. f_equal. rewrite ! Mod.add_list_sk. f_equal.
         rewrite ! map_app. rewrite ! map_map. ss. }
    rewrite ! Mod.add_list_app. rewrite ! ModL_add_fnsems.
    rewrite ! alist_find_app_o.
    hexploit (stb_find_iff_mid_kmd sk_link fn). i. inv H.
    { des. subst. right. left. esplits; et. right. eapply in_map. et. }
    hexploit (stb_find_iff_mid_umd sk_link fn). i. inv H.
    { des. subst. right. right. esplits; et. }
    { left. auto. }
  Qed.

  Variant my_lemma2_r1: forall R0 R1 (RR: R0 -> R1 -> Prop), Ord.t -> itree eventE R0 -> itree eventE R1 -> Prop :=
  | my_lemma2_r1_intro
      R mn (itr: itree _ R) st
      (MN: List.In (Some mn) _frds)
    :
      my_lemma2_r1 eq 200
                   (EventsL.interp_Es (ModSemL.prog (ModL.enclose prog_mid)) (transl_all mn (interp_hEs_src itr)) st)
                   (EventsL.interp_Es (ModSemL.prog (ModL.enclose prog_tgt)) (transl_all mn (interp_hEs_src (KModSem.transl_itr_mid itr))) st)
  .

  Variant my_lemma2_r2: forall R0 R1 (RR: R0 -> R1 -> Prop), Ord.t -> itree eventE R0 -> itree eventE R1 -> Prop :=
  | my_lemma2_r2_intro
      R mn (itr: itree _ R) st
      (MN: ~ List.In (Some mn) _frds)
    :
      my_lemma2_r2 eq 200
                   (EventsL.interp_Es (ModSemL.prog (ModL.enclose prog_mid)) (transl_all mn (interp_hEs_src (massage_itr false itr))) st)
                   (EventsL.interp_Es (ModSemL.prog (ModL.enclose prog_tgt)) (transl_all mn (interp_hEs_src (massage_itr true itr))) st)
  .

  Let my_r := my_lemma2_r1 \6/ my_lemma2_r2.

  Ltac gsteps := HoareDef.steps.

  Lemma my_lemma2_aux
    :
      my_r <6= simg.
  Proof.
    Local Opaque _frds in_dec.
    ginit.
    { i. eapply cpn6_wcompat; eauto with paco. }
    gcofix CIH. i. destruct PR.
    { destruct H. ides itr.
      { gsteps. }
      { gsteps. gbase. eapply CIH. left. econs. auto. }
      rewrite <- bind_trigger. destruct e.
      { resub. destruct h. gsteps. gbase. eapply CIH. left. econs. auto. }
      destruct e.
      { resub. destruct c. gsteps.
        hexploit (stb_find_iff_mid fn). i. des.
        { rewrite SRC. rewrite TGT. gsteps. }
        { rewrite SRC. rewrite TGT. gsteps.
          unfold my_if, sumbool_to_bool. des_ifs.
          unfold fun_to_src, body_to_src. rewrite Any.pair_split. gsteps.
          guclo bindC_spec. econs.
          { gbase. eapply CIH. left. econs. auto. }
          i. subst. destruct vret_tgt as [mp0 retv].
          gsteps.
          gbase. eapply CIH. left. econs. auto.
        }
        { rewrite SRC. rewrite TGT. gsteps.
          unfold fun_to_src, body_to_src. rewrite Any.pair_split. gsteps.
          guclo bindC_spec. econs.
          { gbase. eapply CIH. right. econs. auto. }
          i. subst. destruct vret_tgt as [mp0 retv].
          gsteps.
          gbase. eapply CIH. left. econs. auto.
        }
      }
      destruct s; resub.
      { destruct p.
        { gsteps. gbase. eapply CIH. left. econs. auto. }
        { gsteps. gbase. eapply CIH. left. econs. auto. }
      }
      { destruct e.
        { gsteps. exists x_tgt. gsteps. gbase. eapply CIH. left. econs. auto. }
        { gsteps. exists x_src. gsteps. gbase. eapply CIH. left. econs. auto. }
        { gsteps. gbase. eapply CIH. left. econs. auto. }
      }
    }
    { destruct H. ides itr.
      { ired_both. gsteps. }
      { gsteps. gbase. eapply CIH. right. econs. auto. }
      rewrite <- bind_trigger. destruct e.
      { resub. destruct c. gsteps.
        gsteps. hexploit (stb_find_iff_mid fn). i. des.
        { rewrite SRC. rewrite TGT. gsteps. }
        { rewrite SRC. rewrite TGT. gsteps.
          unfold my_if, sumbool_to_bool. des_ifs.
          unfold fun_to_src, body_to_src. rewrite Any.pair_split. gsteps.
          guclo bindC_spec. econs.
          { gbase. eapply CIH. left. econs. auto. }
          i. subst. destruct vret_tgt as [mp0 retv].
          gsteps.
          gbase. eapply CIH. right. econs. auto.
        }
        { rewrite SRC. rewrite TGT. gsteps.
          unfold fun_to_src, body_to_src. rewrite Any.pair_split. gsteps.
          guclo bindC_spec. econs.
          { gbase. eapply CIH. right. econs. auto. }
          i. subst. destruct vret_tgt as [mp0 retv].
          gsteps.
          gbase. eapply CIH. right. econs. auto.
        }
      }
      destruct s.
      { resub. destruct p.
        { gsteps. gbase. eapply CIH. right. econs. auto. }
        { gsteps. gbase. eapply CIH. right. econs. auto. }
      }
      { resub. destruct e.
        { gsteps. exists x_tgt. gsteps.
          gbase. eapply CIH. right. econs. auto. }
        { gsteps. exists x_src. gsteps.
          gbase. eapply CIH. right. econs. auto. }
        { gsteps. gbase. eapply CIH. right. econs. auto. }
      }
    }
    Unshelve. all: try (exact Ord.O).
  Qed.

  Lemma my_lemma2_sk
    :
      ModL.sk prog_mid = ModL.sk prog_tgt.
  Proof.
    unfold prog_mid, prog_tgt. rewrite ! Mod.add_list_sk.
    unfold Sk.add, Sk.unit.
    rewrite <- ! (@fold_right_app_flat_map _ _ Mod.sk).
    rewrite ! flat_map_app. f_equal.
    { unfold kmds. rewrite ! map_map.
      rewrite ! flat_map_map. eapply flat_map_ext. i. ss. }
    { rewrite ! flat_map_map. eapply flat_map_ext. i. ss. }
  Qed.

  Lemma my_lemma2_initial_mrs
    :
      ModSemL.initial_mrs (ModL.get_modsem prog_mid (Sk.sort (ModL.sk prog_mid))) =
      ModSemL.initial_mrs (ModL.get_modsem prog_tgt (Sk.sort (ModL.sk prog_tgt))).
  Proof.
    rewrite my_lemma2_sk. unfold prog_mid, prog_tgt.
    rewrite ! Mod.add_list_initial_mrs.
    rewrite <- ! fold_right_app_flat_map.
    rewrite ! flat_map_app. f_equal.
    { unfold kmds. rewrite map_map. rewrite ! flat_map_map.
      eapply flat_map_ext. i. ss. }
    { rewrite ! flat_map_map.
      eapply flat_map_ext. i. ss. }
  Qed.

  Lemma my_lemma2_initial_state
    :
      (ModSemL.initial_p_state (ModL.enclose prog_mid))
      =
      (ModSemL.initial_p_state (ModL.enclose prog_tgt)).
  Proof.
    unfold ModL.enclose.
    unfold ModSemL.initial_p_state.
    rewrite my_lemma2_initial_mrs. auto.
  Qed.

  Definition midConf: EMSConfig := {| finalize := finalize; initial_arg := Any.pair true↑ initial_arg |}.

  Lemma my_lemma2:
    Beh.of_program (@ModL.compile midConf (Mod.add_list (List.map SMod.to_src kmds ++ List.map (SMod.to_src ∘ massage_md true) umds))) <1=
    Beh.of_program (@ModL.compile CONF (Mod.add_list (List.map (KMod.transl_src frds) _kmds ++ List.map (SMod.to_src ∘ massage_md false) umds))).
  Proof.
    eapply adequacy_global_itree; ss.
    exists (200)%ord.
    ginit.
    { eapply cpn6_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr, ModSemL.initial_itr.
    fold prog_tgt. fold prog_mid.
    gsteps. unshelve esplits.
    { inv x_src. econs.
      { inv H. econs.
        { clear wf_initial_mrs.
          match goal with
          | H: List.NoDup ?l0 |- List.NoDup ?l1 => replace l1 with l0; auto
          end.
          unfold ModL.enclose. rewrite my_lemma2_sk. unfold prog_mid, prog_tgt.
          rewrite ! Mod.add_list_fns. rewrite <- ! fold_right_app_flat_map.
          rewrite ! flat_map_app. f_equal.
          { unfold kmds. rewrite map_map. rewrite ! flat_map_map.
            eapply flat_map_ext. i. ss.
            rewrite ! map_map. f_equal. extensionality x.
            destruct x. ss. }
          { rewrite ! flat_map_map. eapply flat_map_ext.
            i. ss. rewrite ! map_map. f_equal.
            extensionality x. destruct x. ss. }
        }
        { unfold ModL.enclose. rewrite <- my_lemma2_initial_mrs. auto. }
      }
      { rewrite <- my_lemma2_sk. auto. }
    }
    unfold ITree.map. gsteps.
    hexploit (stb_find_iff_mid "main"). i. des.
    { rewrite SRC. rewrite TGT. gsteps. }
    { rewrite SRC. rewrite TGT. gsteps.
      unfold my_if, sumbool_to_bool. des_ifs.
      unfold fun_to_src, body_to_src. rewrite Any.pair_split. gsteps.
      guclo bindC_spec. econs.
      { gfinal. right.
        rewrite my_lemma2_initial_state. eapply my_lemma2_aux. left. econs. ss. }
      i. subst. gsteps.
    }
    { rewrite SRC. rewrite TGT. gsteps.
      unfold my_if, sumbool_to_bool. des_ifs.
      unfold fun_to_src, body_to_src. rewrite Any.pair_split. gsteps.
      guclo bindC_spec. econs.
      { gfinal. right.
        rewrite my_lemma2_initial_state. eapply my_lemma2_aux. right. econs. ss. }
      i. subst. gsteps.
    }
    Unshelve. all: try (exact Ord.O).
  Qed.

  Lemma my_lemma3_aux md
    :
      ModPair.sim (addtau_md md) (SMod.to_src (massage_md false md)).
  Proof.
    econs; ss. i.
    eapply ModSemPair.mk with (wf:=fun (_: unit) '(mp_src, mp_tgt) => mp_src = mp_tgt) (le:=top2).
    { ss. }
    { ss. rewrite ! map_map.
      eapply Forall2_apply_Forall2.
      { refl. }
      i. subst. destruct b as [fn f]. ss. econs.
      { ss. }
      ii. subst.
      exists 100. ginit. unfold fun_to_src, body_to_src. ss. destruct y.
      unfold addtau_ktr.
      generalize (f (o, t)).
      revert mrs_tgt.
      gcofix CIH. i. ides i.
      { steps. }
      { steps. gbase. eapply CIH. }
      rewrite <- bind_trigger. destruct e.
      { resub. destruct c. steps. gstep. econs; et. i.
        eexists. steps. destruct w1.
        guclo lordC_spec. econs.
        { eapply OrdArith.add_base_l. }
        gbase. eapply CIH.
      }
      destruct s.
      { resub. destruct p.
        { ired_both. force_r. steps.
          gbase. eapply CIH. }
        { ired_both. force_r. steps.
          gbase. eapply CIH.
        }
      }
      { resub. destruct e.
        { ired_both. resub. force_r. i. steps. force_l. exists x. steps.
          guclo lordC_spec. econs.
          { eapply OrdArith.add_base_l. }
          gbase. eapply CIH.
        }
        { ired_both. resub. force_l. force_l. i.
          force_r. exists x. steps.
          guclo lordC_spec. econs.
          { eapply OrdArith.add_base_l. }
          gbase. eapply CIH.
        }
        { ired_both. resub. steps. gstep. econs. i. esplits.
          steps. guclo lordC_spec. econs.
          { eapply OrdArith.add_base_l. }
          gbase. eapply CIH.
        }
      }
    }
    { ss. }
    { exists tt. ss. }
  Unshelve. all: try (exact 0).
  Qed.

  Lemma my_lemma3:
    Beh.of_program (ModL.compile (Mod.add_list (List.map (KMod.transl_src frds) _kmds ++ List.map (SMod.to_src ∘ massage_md false) umds))) <1=
    Beh.of_program (ModL.compile (Mod.add_list (List.map (KMod.transl_src frds) _kmds ++ umds))).
  Proof.
    eapply refines_close.
    transitivity (Mod.add_list (map (KMod.transl_src frds) _kmds ++ map addtau_md umds)).
    { eapply adequacy_local_list. eapply Forall2_app.
      { eapply Forall2_impl.
        { refl. }
        i. subst. eapply ModPair.self_sim.
      }
      { eapply Forall2_apply_Forall2.
        { refl. }
        i. subst. eapply my_lemma3_aux.
      }
    }
    { eapply adequacy_local_list. eapply Forall2_app.
      { eapply Forall2_impl.
        { refl. }
        i. subst. eapply ModPair.self_sim.
      }
      { erewrite <- (map_id umds) at 1. eapply Forall2_apply_Forall2.
        { refl. }
        i. subst. eapply adequacy_rmtau.
      }
    }
  Qed.

  Let stb2 :=
    (map (fun '(fn0, fs) => (fn0, ((fs: fspecbody): fspec)))
         (flat_map SModSem.fnsems
                   (map
                      (flip SMod.get_modsem
                            (Sk.sort
                               (foldr Sk.add Sk.unit
                                      (map SMod.sk (kmds ++ map (massage_md true) umds)))))
                      (kmds ++ map (massage_md true) umds)))).

  Let stb2_eq fn:
    _stb (Sk.sort (foldr Sk.add Sk.unit (map SMod.sk (kmds ++ map (massage_md true) umds)))) fn
    =
    match alist_find fn stb2 with
    | Some fsp => Some fsp
    | _ => Some (KModSem.disclose_mid fspec_trivial)
    end.
  Proof.
    set (sk := Sk.sort (foldr Sk.add Sk.unit (map SMod.sk (kmds ++ map (massage_md true) umds)))).
    replace stb2 with
        ((map (map_snd KModSem.disclose_mid) (_gstb sk))
           ++
           (map (map_snd (fun _ => KModSem.disclose_mid fspec_trivial)) (flat_map ModSem.fnsems (map (flip Mod.get_modsem sk) umds)))).
    2:{
      unfold _gstb, stb2, KMod.get_stb, kmds. unfold kmds in sk. fold sk.
      rewrite ! map_app. rewrite flat_map_app. rewrite map_app. f_equal.
      { rewrite map_map. rewrite ! flat_map_map. rewrite ! map_flat_map.
        ss. rewrite ! flat_map_map. eapply flat_map_ext.
        i. rewrite map_map. eapply map_ext. intros []. ss. }
      { rewrite map_map. rewrite ! flat_map_map. rewrite ! map_flat_map.
        ss. rewrite ! flat_map_map. eapply flat_map_ext.
        i. rewrite map_map. eapply map_ext. intros []. ss. }
    }
    { unfold _stb. rewrite alist_find_app_o. rewrite ! alist_find_map_snd.
      uo. des_ifs. }
  Qed.

  Hypothesis MAINM:
    True ->
    let sk := (Sk.sort (foldr Sk.add Sk.unit (map SMod.sk (kmds ++ map (massage_md true) umds)))) in
    exists (entry_r: Σ),
      (<<WFR: URA.wf (entry_r ⋅ KMod.get_initial_mrs _kmds sk)>>) /\
      (<<MAIN: forall (main_fsp: fspec)
                      (MAIN: alist_find "main" (KMod.get_stb _kmds sk) = Some main_fsp),
          exists (x: main_fsp.(meta)),
            (<<PRE: main_fsp.(precond) None x initial_arg initial_arg ord_top entry_r>>) /\
            (<<RET: forall ret_src ret_tgt r
                           (POST: main_fsp.(postcond) None x ret_src ret_tgt r),
                ret_src = ret_tgt>>)>>).

  Theorem adequacy_open_aux1':
    refines_closed (Mod.add_list (List.map (SMod.to_tgt _stb) kmds ++ umds))
                   (Mod.add_list (List.map (KMod.transl_src frds) _kmds ++ umds))
  .
  Proof.
    transitivity (Mod.add_list (List.map (SMod.to_tgt _stb) kmds ++ List.map (SMod.to_tgt _stb ∘ massage_md true) umds)).
    { eapply refines_close.
      transitivity (Mod.add_list (map (SMod.to_tgt _stb) kmds ++ map addtau_md umds)).
      { eapply adequacy_local_list. eapply Forall2_app.
        { eapply Forall2_impl.
          { refl. }
          i. subst. eapply ModPair.self_sim.
        }
        { erewrite <- (map_id umds) at 2. eapply Forall2_apply_Forall2.
          { refl. }
          i. subst. eapply adequacy_addtau.
        }
      }
      { eapply adequacy_local_list. eapply Forall2_app.
        { eapply Forall2_impl.
          { refl. }
          i. subst. eapply ModPair.self_sim.
        }
        { eapply Forall2_apply_Forall2.
          { refl. }
          i. subst. eapply my_lemma1. auto.
        }
      }
    }
    ii. eapply my_lemma3. eapply my_lemma2.
    rewrite <- (map_map (massage_md true)). rewrite <- map_app.
    eapply adequacy_type_arg_stb; ss.
    { i. instantiate (1:=_stb).
      rewrite stb2_eq. unfold stb2.
      unfold SMod.get_sk in FIND. rewrite FIND. auto. }
    { i. unfold SMod.get_sk in FIND. rewrite stb2_eq. right.
      unfold stb2. rewrite FIND. esplits; et.
      i. ss. destruct x; des; auto.
      red in PRE0. uipropall. des; auto. }
    { hexploit MAINM; et. i. des. unfold _stb, _gstb, KMod.get_stb in MAIN.
      assert (RWF: URA.wf
                     (entry_r
                        ⋅ fold_left URA.add
                        (map SModSem.initial_mr
                             (map
                                (flip SMod.get_modsem
                                      (SMod.get_sk (kmds ++ map (massage_md true) umds)))
                                (kmds ++ map (massage_md true) umds))) ε)).
      { match goal with
        | H: URA.wf ?r0 |- URA.wf ?r1 => replace r1 with r0; auto
        end.
        f_equal. unfold KMod.get_initial_mrs.
        rewrite map_map. ss. unfold SMod.get_sk.
        generalize (Sk.sort
                      (foldr Sk.add Sk.unit
                             (map SMod.sk (kmds ++ map (massage_md true) umds)))).
        i. unfold kmds. rewrite map_app. rewrite ! map_map. ss.
        rewrite fold_left_app.
        generalize (fold_left
                      URA.add
                      (map (fun x=>  KModSem.initial_mr (KMod.get_modsem x t)) _kmds) ε).
        i. generalize umds. i. induction umds0; ss.
        rewrite URA.unit_id. auto.
      }
      rewrite alist_find_map_snd in MAIN. uo. des_ifs.
      { hexploit MAIN0.
        { instantiate (1:=k). unfold KMod.get_stb.
          rewrite alist_find_map_snd. uo.
          match goal with
          | H: alist_find _ ?l0 = Some _ |- context[alist_find _ ?l1] =>
            replace l1 with l0
          end.
          { rewrite Heq0. auto. }
          eapply flat_map_ext. i. ss.
        }
        i. des. exists (Some x), entry_r. splits; auto.
        { ss. esplits; et. }
        { i. ss. uipropall. i. red. uipropall. eapply RET; et. }
      }
      { exists (Some tt). exists entry_r. splits; auto.
        { ss. esplits; et. red. uipropall. }
      }
    }
    match goal with
    | H: Beh.of_program ?p0 x0 |- Beh.of_program ?p1 x0 => replace p1 with p0
    end.
    { auto. }
    rewrite map_app. rewrite map_map. auto.
  Qed.

  End UMDS.

  (* TODO: move it to ModSem *)
  Lemma ModL_add_fnsems md0 md1 sk
    :
      (ModSemL.initial_mrs (ModL.get_modsem (ModL.add md0 md1) sk)) =
      (ModSemL.initial_mrs (ModL.get_modsem md0 sk)) ++ (ModSemL.initial_mrs (ModL.get_modsem md1 sk)).
  Proof.
    ss.
  Qed.

  Lemma adequacy_open_aux1
        (MAINM:
           forall sk (SKWF: Sk.wf sk) (SKINCL: Sk.incl (KMod.get_sk _kmds) sk),
           exists (entry_r: Σ),
             (<<WFR: URA.wf (entry_r ⋅ KMod.get_initial_mrs _kmds sk)>>) /\
             (<<MAIN: forall (main_fsp: fspec)
                             (MAIN: alist_find "main" (KMod.get_stb _kmds sk) = Some main_fsp),
                 exists (x: main_fsp.(meta)),
                   (<<PRE: main_fsp.(precond) None x initial_arg initial_arg ord_top entry_r>>) /\
                   (<<RET: forall ret_src ret_tgt r
                                  (POST: main_fsp.(postcond) None x ret_src ret_tgt r),
                       ret_src = ret_tgt>>)>>))
    :
      refines (Mod.add_list (List.map (SMod.to_tgt _stb) kmds))
              (Mod.add_list (List.map (KMod.transl_src frds) _kmds))
  .
  Proof.
    ii. eapply ModL.add_comm. eapply ModL.add_comm in PR.
    rewrite <- Mod.add_list_app in *.
    destruct (classic (ModL.wf (Mod.add_list (map (KMod.transl_src frds) _kmds ++ ctx)))).
    2: { unfold ModL.compile. eapply ModSemL.compile_not_wf. et. }
    eapply adequacy_open_aux1'; auto.
    { i. ss. des; ss. eapply in_map_iff in MIN0. des. clarify.
      inv H. inv H0. unfold ModL.enclose in wf_initial_mrs.
      replace (Sk.sort
                 (ModL.sk
                    (Mod.add_list
                       (map (KMod.transl_src frds) _kmds ++ ctx)))) with
          (Sk.sort (foldr Sk.add Sk.unit (map SMod.sk kmds ++ map Mod.sk ctx)))
          in wf_initial_mrs.
      { rewrite Mod.add_list_app in wf_initial_mrs.
        rewrite ModL_add_fnsems in wf_initial_mrs.
        rewrite map_app in wf_initial_mrs.
        eapply NoDup_app_disjoint in wf_initial_mrs; ss.
        { instantiate (1:=mn).
          rewrite Mod.add_list_initial_mrs. ss.
          rewrite <- fold_right_app_flat_map.
          rewrite flat_map_single. rewrite ! map_map. ss. }
        { rewrite Mod.add_list_initial_mrs. ss.
          rewrite <- fold_right_app_flat_map.
          rewrite flat_map_single. rewrite ! map_map. ss. }
      }
      { rewrite Mod.add_list_sk. rewrite map_app. unfold kmds.
        f_equal. f_equal. f_equal. rewrite ! map_map. ss. }
    }
    i. subst sk. eapply MAINM.
    { inv H. red in H2. eapply Sk.sort_wf.
      match goal with
      | H: Sk.wf ?l0 |- Sk.wf ?l1 => replace l1 with l0; auto
      end.
      rewrite Mod.add_list_sk. f_equal. unfold kmds.
      rewrite ! map_app. rewrite ! map_map. auto.
    }
    { etrans; [|eapply Sk.sort_incl]. etrans; [eapply Sk.sort_incl_rev|].
      unfold kmds. unfold Sk.t, Sk.add, Sk.unit, alist.
      rewrite <- ! fold_right_app_flat_map.
      rewrite flat_map_app. ii. eapply in_or_app. left.
      rewrite flat_map_map. ss.
    }
  Qed.

End ADQ.


Require Import HTactics.

Section ADQ.
  Context {CONF: EMSConfig}.
  Context `{Σ: GRA.t}.
  Variable _kmds: list KMod.t.

  Let frds: Sk.t -> list mname := KMod.get_frds _kmds.

  Let _kmss: Sk.t -> list KModSem.t := fun ske => List.map (flip KMod.get_modsem ske) _kmds.

  Let _gstb: Sk.t -> list (gname * fspec) := KMod.get_stb _kmds.

  Let _stb: Sk.t -> gname -> option fspec := fun sk => to_closed_stb (_gstb sk).

  Let kmds_mid: list SMod.t := List.map KMod.transl_mid _kmds.
  Let _kmss_mid: Sk.t -> list SModSem.t := fun ske => List.map (flip SMod.get_modsem ske) kmds_mid.

  Let _stb_mid: Sk.t -> gname -> option fspec :=
    fun sk fn => match alist_find fn (_gstb sk) with
                 | Some fsp => Some (KModSem.disclose_mid fsp)
                 | _ => Some (KModSem.disclose_mid fspec_trivial)
                 end.

  Let stb_find_iff (sk: Sk.t) (fn: gname) (fsp: fspec)
      (FIND: _stb sk fn = Some fsp)
    :
      _stb_mid sk fn = Some (KModSem.disclose_mid fsp).
  Proof.
    unfold _stb, to_closed_stb in FIND. unfold _stb_mid. des_ifs.
  Qed.

  Let kmds: list Mod.t := List.map (KMod.transl_tgt _stb) _kmds.

  Lemma adequacy_open_aux2_hcall
    :
      forall mp (mr: Σ) w mn o fsp fn arg ctx tbr,
        paco7 (_sim_itree (fun (_: unit) '(st_src, st_tgt) =>
                             exists st (mr: Σ),
                               st_src = Any.pair st mr↑ /\ st_tgt = Any.pair st mr↑) top2)
              bot7 (Σ * Any.t)%type (Σ * Any.t)%type
              (fun st_src st_tgt ret_src ret_tgt =>
                 exists st (mr: Σ),
                   st_src = Any.pair st mr↑ /\ st_tgt = Any.pair st mr↑ /\ ret_src = ret_tgt)
              20%ord w
              (Any.pair mp mr↑,
                        HoareCall mn tbr o (KModSem.disclose_mid fsp) fn (Any.pair true↑ arg) ctx)
              (Any.pair mp mr↑,
                        HoareCall mn tbr o fsp fn arg ctx).
  Proof.
    i. ginit.
    Local Transparent HoareCall. unfold HoareCall. Local Opaque HoareCall.
    unfold mput, mget. steps.
    force_l. eexists (c0, c1, c). steps.
    force_l; auto. steps. force_l. exists (Some x). steps.
    force_l. eexists. force_l. eexists. force_l.
    { esplits; et. }
    steps. force_l; auto. steps.
    gstep. econs; et. i. des. clarify. exists 100.
    steps. force_r. eexists (c2, c3). steps.
    force_r; auto. steps. force_r. eexists.
    force_r; et. steps.
  Qed.

  Lemma adequacy_open_aux2_apc sk
    :
      forall mp (mr: Σ) w mn o ctx,
        paco7 (_sim_itree (fun (_: unit) '(st_src, st_tgt) =>
                             exists st (mr: Σ),
                               st_src = Any.pair st mr↑ /\ st_tgt = Any.pair st mr↑) top2)
              bot7 (Σ * unit)%type (Σ * unit)%type
              (fun st_src st_tgt ret_src ret_tgt =>
                 exists st (mr: Σ),
                   st_src = Any.pair st mr↑ /\ st_tgt = Any.pair st mr↑ /\ ret_src = ret_tgt)
              100%ord w
              (Any.pair mp mr↑,
                        interp_hCallE_tgt mn
                        (_stb_mid sk) o
                        APC
                        ctx)
              (Any.pair mp mr↑,
                        interp_hCallE_tgt mn
                        (_stb sk) o
                        APC
                        ctx).
  Proof.
    ginit. i.
    Local Transparent APC. unfold APC. Local Opaque APC.
    steps. force_l. exists x. steps. force_l; auto. steps.
    clear _GUARANTEE _GUARANTEE0.
    revert x mp mr w mn o ctx. gcofix CIH. i.
    rewrite unfold_APC. steps. force_l. exists x0. steps. destruct x0.
    { steps. }
    steps. force_l. exists x0. steps. force_l; auto. steps.
    force_l. exists (s, Any.pair true↑ t). steps.
    hexploit stb_find_iff; et. i. rewrite H. steps.
    guclo lordC_spec. econs.
    { instantiate (1:=(50 + 20)%ord).
      rewrite <- OrdArith.add_from_nat.
      eapply OrdArith.le_from_nat. lia. }
    guclo lbindC_spec. econs.
    { gfinal. right. eapply paco7_mon.
      { eapply adequacy_open_aux2_hcall. }
      { ss. }
    }
    i. ss. des; clarify.
    destruct vret_tgt as [ctx0 vret]. ired_both. steps.
    gbase. eapply CIH.
    Unshelve. all: ss.
  Qed.

  Lemma adequacy_open_aux2_itr sk
    :
      forall R mp (mr: Σ) w mn o itr ctx,
        paco7 (_sim_itree (fun (_: unit) '(st_src, st_tgt) =>
                             exists st (mr: Σ),
                               st_src = Any.pair st mr↑ /\ st_tgt = Any.pair st mr↑) top2)
              bot7 (Σ * R)%type (Σ * R)%type
              (fun st_src st_tgt ret_src ret_tgt =>
                 exists st (mr: Σ),
                   st_src = Any.pair st mr↑ /\ st_tgt = Any.pair st mr↑ /\ ret_src = ret_tgt)
              200%ord w
              (Any.pair mp mr↑,
                        interp_hCallE_tgt mn
                        (_stb_mid sk) o
                        (interp_hEs_tgt (KModSem.transl_itr_mid itr))
                        ctx)
              (Any.pair mp mr↑,
                        interp_hCallE_tgt mn
                        (_stb sk) o (interp_hEs_tgt itr)
                        ctx).
  Proof.
    ginit. gcofix CIH. i. ides itr.
    { steps. }
    { steps. gbase. et. }
    rewrite <- bind_trigger. ired_both.
    destruct e.
    { resub. destruct h. steps.
      guclo lordC_spec. econs.
      { instantiate (1:=(50 + 100)%ord).
        rewrite <- OrdArith.add_from_nat.
        eapply OrdArith.le_from_nat. lia. }
      guclo lbindC_spec. econs.
      { gfinal. right. eapply paco7_mon.
        { eapply adequacy_open_aux2_apc. }
        { ss. }
      }
      i. ss. des; clarify. destruct vret_tgt as [ctx0 vret].
      steps. guclo lordC_spec. econs.
      { eapply OrdArith.add_base_l. }
      gbase. eapply CIH.
    }
    destruct e.
    { resub. destruct c. steps.
      hexploit stb_find_iff; et. i. rewrite H. steps.
      guclo lordC_spec. econs.
      { instantiate (1:=(50 + 20)%ord).
        rewrite <- OrdArith.add_from_nat.
        eapply OrdArith.le_from_nat. lia. }
      guclo lbindC_spec. econs.
      { gfinal. right. eapply paco7_mon.
        { eapply adequacy_open_aux2_hcall. }
        { ss. }
      }
      i. ss. des; clarify. destruct vret_tgt as [ctx0 vret].
      steps. guclo lordC_spec. econs.
      { eapply OrdArith.add_base_l. }
      gbase. eapply CIH.
    }
    destruct s.
    { resub. destruct p.
      { ired_both. force_l. force_l. force_r. force_r. steps.
        guclo lordC_spec. econs.
        { eapply OrdArith.add_base_l. }
        gbase. eapply CIH.
      }
      { ired_both. force_l. force_l. force_r. force_r. steps.
        guclo lordC_spec. econs.
        { eapply OrdArith.add_base_l. }
        gbase. eapply CIH.
      }
    }
    { resub. destruct e.
      { ired_both. force_r. i. force_l. exists x.
        ired_both. steps.
        guclo lordC_spec. econs.
        { eapply OrdArith.add_base_l. }
        gbase. eapply CIH.
      }
      { ired_both. force_l. i. force_r. exists x.
        ired_both. steps.
        guclo lordC_spec. econs.
        { eapply OrdArith.add_base_l. }
        gbase. eapply CIH.
      }
      { steps. gstep. econs. i. eexists. steps.
        guclo lordC_spec. econs.
        { eapply OrdArith.add_base_l. }
        gbase. eapply CIH.
      }
    }
    Unshelve. all: ss; try (exact 0).
  Qed.

  Lemma adequacy_open_aux2:
    refines (Mod.add_list kmds)
            (Mod.add_list (List.map (SMod.to_tgt _stb_mid) kmds_mid)).
  Proof.
    unfold kmds. eapply adequacy_local_list.
    unfold kmds_mid. rewrite List.map_map.
    eapply Forall2_apply_Forall2.
    { refl. }
    i. subst. econs; ss. i. econs; ss.
    { instantiate (1:=fun (_ _: unit) => True). ss. }
    { instantiate (1:=fun _ '(st_src, st_tgt) =>
                        exists st (mr: Σ),
                          st_src = Any.pair st mr↑ /\ st_tgt = Any.pair st mr↑).
      rewrite List.map_map.
      eapply Forall2_apply_Forall2.
      { refl. }
      i. subst. destruct b0 as [fn ksb]. ss. econs; ss.
      ii. subst. ss. exists 300. ginit.
      unfold KModSem.disclose_ksb_tgt, fun_to_tgt. ss.
      Local Transparent HoareFun. unfold HoareFun. Local Opaque HoareFun.
      des. clarify. unfold mget, mput. steps. destruct x.
      { des; clarify. force_r. exists true.
        force_r. exists m. force_r. eexists _.
        force_r. exists (c, c0). force_r. force_r; auto.
        force_r. eexists _. force_r; eauto.
        steps. destruct x1.
        { steps. guclo lordC_spec. econs.
          { instantiate (1:=(50 + 100)%ord).
            rewrite <- OrdArith.add_from_nat.
            eapply OrdArith.le_from_nat. lia. }
          guclo lbindC_spec. econs.
          { gfinal. right. eapply paco7_mon.
            { eapply adequacy_open_aux2_apc. }
            { ss. }
          }
          i. ss. des; clarify. destruct vret_tgt as [ctx0 vret].
          steps. force_l. eexists. steps.
          force_l. eexists. force_l. eexists (c1, c2). steps.
          force_l; et. force_l; et.
          steps. econs; ss. esplits; et.
        }
        { steps. guclo lordC_spec. econs.
          { instantiate (1:=(50 + 200)%ord).
            rewrite <- OrdArith.add_from_nat.
            eapply OrdArith.le_from_nat. lia. }
          guclo lbindC_spec. econs.
          { gfinal. right. eapply paco7_mon.
            { eapply adequacy_open_aux2_itr. }
            { ss. }
          }
          i. ss. des; clarify. destruct vret_tgt as [ctx0 vret].
          steps. force_l. eexists. steps.
          force_l. eexists (c1, c2). steps.
          force_l; et. force_l; et.
          steps. econs; ss. esplits; et.
        }
      }
      { des; clarify. force_r. exists false.
        force_r. exists tt. force_r. exists t.
        force_r. exists (c, c0). force_r. force_r; auto.
        force_r. exists ord_top. force_r.
        { red. uipropall. }
        steps.
        guclo lordC_spec. econs.
        { instantiate (1:=(50 + 200)%ord).
          rewrite <- OrdArith.add_from_nat.
          eapply OrdArith.le_from_nat. lia. }
        guclo lbindC_spec. econs.
        { gfinal. right. eapply paco7_mon.
          { eapply adequacy_open_aux2_itr. }
          { ss. }
        }
        i. ss. des; clarify. destruct vret_tgt as [ctx0 vret].
        steps. force_l. eexists.
        force_l. eexists (c1, c2). steps.
        force_l; et. force_l.
        { red in _GUARANTEE0. uipropall. }
        steps. econs; ss. esplits; et.
      }
    }
    { exists tt. esplits; et. }
    Unshelve. all: ss.
  Qed.
End ADQ.


Section ADQ.
  Context {CONF: EMSConfig}.

  Context `{Σ: GRA.t}.
  Variable kmds: list KMod.t.

  Theorem adequacy_open
          (MAINM:
             forall sk (SKWF: Sk.wf sk) (SKINCL: Sk.incl (KMod.get_sk kmds) sk),
             exists (entry_r: Σ),
               (<<WFR: URA.wf (entry_r ⋅ KMod.get_initial_mrs kmds sk)>>) /\
               (<<MAIN: forall (main_fsp: fspec)
                               (MAIN: alist_find "main" (KMod.get_stb kmds sk) = Some main_fsp),
                   exists (x: main_fsp.(meta)),
                     (<<PRE: main_fsp.(precond) None x initial_arg initial_arg ord_top entry_r>>) /\
                     (<<RET: forall ret_src ret_tgt r
                                    (POST: main_fsp.(postcond) None x ret_src ret_tgt r),
                         ret_src = ret_tgt>>)>>))
    :
      refines2 (KMod.transl_tgt_list kmds)
               (KMod.transl_src_list kmds).
  Proof.
    etrans.
    { eapply adequacy_open_aux2. }
    { eapply adequacy_open_aux1; et. }
  Qed.
End ADQ.

Require Import Weakening.

Section WEAKEN.

  Context `{Σ: GRA.t}.

  Theorem kmod_adequacy_weaken
          stb0 stb1
          md
          (WEAK: forall sk, stb_weaker (stb0 sk) (stb1 sk))
    :
      refines2 [KMod.transl_tgt stb0 md] [KMod.transl_tgt stb1 md]
  .
  Proof.
    eapply adequacy_local2.
    econs; cycle 1.
    { unfold KMod.transl_tgt. cbn. eauto. }
    i. specialize (WEAK sk). r. econs.
    2:{ unfold KMod.transl_tgt. ss.
        abstr (KModSem.fnsems (KMod.get_modsem md sk)) fnsems.
        eapply Forall2_apply_Forall2.
        { refl. }
        i. subst. destruct b. split.
        { rr. cbn. ss. }
        ii. subst. exists 201. ss.
        unfold KModSem.disclose_ksb_tgt.
        ginit. gstep. econs. i. exists x_src. exists 200.
        gfinal. right. instantiate (1:=unit) in w. destruct w.
        destruct x_src.
        { eapply weakening_fn; et. refl. }
        { eapply weakening_fn; et. refl. }
    }
    { ss. }
    { ss. }
    exists tt. esplits; et.
  Qed.

End WEAKEN.
