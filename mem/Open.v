Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic.
(* Require Import Mem0 MemOpen. *)
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

Lemma flat_map_map A B C (f: A -> B) (g: B -> list C) (l: list A)
  :
    flat_map g (map f l) = flat_map (g ∘ f) l.
Proof.
  induction l; ss. f_equal; auto.
Qed.

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
  Context `{Σ: GRA.t}.

  Definition addtau_ms (ms: ModSem.t): ModSem.t := {|
    ModSem.fnsems := map (map_snd (addtau_ktr(T:=_))) ms.(ModSem.fnsems);
    ModSem.mn := ms.(ModSem.mn);
    ModSem.initial_mr := ms.(ModSem.initial_mr);
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
      generalize (f y). generalize (@URA.unit (GRA.to_URA Σ)).
      destruct mrs_tgt. revert w c t.
      pcofix CIH. i. ides i.
      { pfold. rewrite addtau_ret. econs; et. }
      { pfold. rewrite addtau_tau. econs; et. }
      { rewrite <- bind_trigger. resub.
        rewrite addtau_bind. rewrite addtau_event.
        rewrite bind_tau. rewrite bind_bind.
        pfold. econs; [ord_tac|].
        left. destruct e.
        { destruct c1. resub. pfold. econs; et. i. subst.
          esplits. left. rewrite bind_tau. pfold. econs; [ord_tac|].
          right. rewrite bind_ret_l. destruct mrs_tgt1. eapply CIH.
        }
        destruct s.
        { resub. destruct r0.
          { pfold. econs; et. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
          { pfold. econs; et. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
          { pfold. econs; et. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
          { pfold. econs; et. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
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
      generalize (f y). generalize (@URA.unit (GRA.to_URA Σ)).
      destruct mrs_tgt. revert w c t.
      pcofix CIH. i. ides i.
      { pfold. rewrite addtau_ret. econs; et. }
      { pfold. rewrite addtau_tau. econs; et. }
      { rewrite <- bind_trigger. resub.
        rewrite addtau_bind. rewrite addtau_event.
        rewrite bind_tau. rewrite bind_bind.
        pfold. econs; [ord_tac|].
        left. destruct e.
        { destruct c1. resub. pfold. econs; et. i. subst.
          esplits. left. rewrite bind_tau. pfold. econs; [ord_tac|].
          right. rewrite bind_ret_l. destruct mrs_tgt1. eapply CIH.
        }
        destruct s.
        { resub. destruct r0.
          { pfold. econs; et. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
          { pfold. econs; et. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
          { pfold. econs; et. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
          { pfold. econs; et. left. rewrite bind_tau. pfold. econs; [ord_tac|].
            right. rewrite bind_ret_l. eapply CIH.
          }
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

  Context `{Σ: GRA.t}.

  (* Variant frE: Type -> Type := *)
  (* | FPut' (fr0: Σ): frE unit *)
  (* | FGet': frE Σ *)
  (* . *)
  Variable stb: (list (string * fspec)).

  Definition massage_callE (b: bool): callE ~> stateT Σ (itree Es') :=
    if b
    then
      fun T '(Call fn args) fr0 => _ <- (alist_find fn stb)?;; r <- trigger (hCall false fn (Any.pair false↑ args));; Ret (fr0, r)
    else
      fun T '(Call fn args) fr0 => r <- trigger (hCall false fn args);; Ret (fr0, r)
  .

  Definition massage_rE: rE ~> stateT Σ (itree Es') :=
    fun T re fr0 =>
      match re with
      | FPut fr1 => Ret (fr1, tt)
      | FGet => Ret (fr0, fr0)
      | MPut mr0 =>
        mrst0 <- trigger (PGet);;
        '(_, st0) <- (Any.split mrst0)ǃ;;
        trigger (PPut (Any.pair mr0↑ st0));;;
        Ret (fr0, tt)
      | MGet =>
        mrst0 <- trigger (PGet);;
        '(mr0, _) <- (Any.split mrst0)ǃ;;
        `mr0: Σ <- mr0↓ǃ;;
        Ret (fr0, mr0)
      end
  .

  Definition massage_pE: pE ~> stateT Σ (itree Es') :=
    fun T pe fr0 =>
      match pe with
      | PPut st0 =>
        mrst0 <- trigger (PGet);;
        '(mr0, _) <- (Any.split mrst0)ǃ;;
        trigger (PPut (Any.pair mr0 st0 ));;;
        Ret (fr0, tt)
      | PGet =>
        mrst0 <- trigger (PGet);;
        '(_, st0) <- (Any.split mrst0)ǃ;;
        Ret (fr0, st0)
      end
  .

  Definition massage_itr b: itree Es ~> stateT Σ (itree Es') :=
    (* interp (case_ (massage_callE) (case_ (massage_rE) (case_ (massage_pE) trivial_state_Handler))) *)
    interp_state (case_ (massage_callE b) (case_ (massage_rE) (case_ (massage_pE) trivial_state_Handler)))
  .

  Definition massage_fun (b: bool) (ktr: (option mname * Any.t) -> itree Es Any.t): ((option mname * Any.t) -> itree Es' Any.t) :=
    if b
    then
      fun '(mn, args) =>
        '(_, args) <- (Any.split args)ǃ;;
        '(_, rv) <- massage_itr b (ktr (mn, args)) ε;; Ret rv
    else
      fun '(mn, args) =>
        '(_, rv) <- massage_itr b (ktr (mn, args)) ε;; Ret rv
  .

  Definition massage_fsb b: ((option mname * Any.t) -> itree Es Any.t) -> fspecbody :=
    fun ktr => mk_specbody (KModSem.disclose_tgt fspec_trivial) (massage_fun b ktr)
  .

  Definition massage_ms b (ms: ModSem.t): SModSem.t := {|
    SModSem.fnsems := List.map (map_snd (massage_fsb b)) ms.(ModSem.fnsems);
    SModSem.mn := ms.(ModSem.mn);
    SModSem.initial_mr := ε;
    SModSem.initial_st := Any.pair (ms.(ModSem.initial_mr))↑ (ms.(ModSem.initial_st));
                                                      |}
  .



  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)

  Lemma massage_itr_bind b
        (R S: Type)
        fr0 (s: itree _ R) (k : R -> itree _ S)
    :
      (massage_itr b (s >>= k)) fr0
      =
      ((massage_itr b s fr0) >>= (fun '(fr1, r) => massage_itr b (k r) fr1)).
  Proof.
    unfold massage_itr in *. rewrite interp_state_bind. grind. des_ifs.
  Qed.

  Lemma massage_itr_tau b
        (U: Type)
        (t : itree _ U) fr0
    :
      (massage_itr b (tau;; t) fr0)
      =
      (tau;; (massage_itr b t) fr0).
  Proof.
    unfold massage_itr in *. rewrite interp_state_tau. grind.
  Qed.

  Lemma massage_itr_ret b
        (U: Type)
        (t: U) fr0
    :
      ((massage_itr b (Ret t)) fr0)
      =
      Ret (fr0, t).
  Proof.
    unfold massage_itr in *. rewrite interp_state_ret. grind.
  Qed.

  Lemma massage_itr_pe b
        (R: Type)
        (i: pE R) fr0
    :
      (massage_itr b (trigger i) fr0)
      =
      (massage_pE i fr0 >>= (fun r => tau;; Ret r)).
  Proof.
    unfold massage_itr in *. rewrite interp_state_trigger. grind.
  Qed.

  Lemma massage_itr_re b
        (R: Type)
        (i: rE R) fr0
    :
      (massage_itr b (trigger i) fr0)
      =
      (massage_rE i fr0 >>= (fun r => tau;; Ret r)).
  Proof.
    unfold massage_itr in *. rewrite interp_state_trigger. grind.
  Qed.

  Lemma massage_itr_calle b
        (R: Type)
        (i: callE R) fr0
    :
      (massage_itr b (trigger i) fr0)
      =
      ((massage_callE b i fr0) >>= (fun r => tau;; Ret r)).
  Proof.
    unfold massage_itr in *. grind.
  Qed.

  Lemma massage_itr_evente b
        (R: Type)
        (i: eventE R) fr0
    :
      (massage_itr b (trigger i) fr0)
      =
      ((trigger i) >>= (fun r => tau;; Ret (fr0, r))).
  Proof.
    unfold massage_itr in *. grind. unfold trivial_state_Handler. grind.
  Qed.

  Lemma massage_itr_triggerUB b
        (R: Type) fr0
    :
      (massage_itr b (triggerUB) fr0)
      =
      triggerUB (A:=(Σ * R)).
  Proof.
    unfold massage_itr, triggerUB in *. rewrite unfold_interp_state. cbn.
    unfold trivial_state_Handler. grind.
  Qed.

  Lemma massage_itr_triggerNB b
        (R: Type) fr0
    :
      (massage_itr b (triggerNB) fr0)
      =
      triggerNB (A:=(Σ * R)).
  Proof.
    unfold massage_itr, triggerNB in *. rewrite unfold_interp_state. cbn.
    unfold trivial_state_Handler. grind.
  Qed.

  Lemma massage_itr_unwrapU b
        (R: Type)
        (i: option R) fr0
    :
      (massage_itr b (unwrapU i) fr0)
      =
      r <- (unwrapU i);; Ret (fr0, r).
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
        (i: option R) fr0
    :
      (massage_itr b (unwrapN i) fr0)
      =
      r <- (unwrapN i);; Ret (fr0, r).
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
        P fr0
    :
      (massage_itr b (assume P) fr0)
      =
      (assume P;;; tau;; Ret (fr0, tt))
  .
  Proof.
    unfold assume. rewrite massage_itr_bind. rewrite massage_itr_evente. grind. eapply massage_itr_ret.
  Qed.

  Lemma massage_itr_guarantee b
        P fr0
    :
      (massage_itr b (guarantee P) fr0)
      =
      (guarantee P;;; tau;; Ret (fr0, tt)).
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

  Definition massage_md (_stb: Sk.t -> (list (string * fspec))) b (md: Mod.t): SMod.t := {|
    SMod.get_modsem := fun sk => massage_ms (_stb sk) b (Mod.get_modsem md sk);
    SMod.sk := md.(Mod.sk);
  |}
  .

  Global Program Instance transl_itr_rdb: red_database (mk_box (@massage_itr)) :=
    mk_rdb
      1
      (mk_box massage_itr_bind)
      (mk_box massage_itr_tau)
      (mk_box massage_itr_ret)
      (mk_box massage_itr_calle)
      (mk_box massage_itr_re)
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
  Context `{Σ: GRA.t}.

  Variable _kmds: list KMod.t.
  Let frds: Sk.t -> list mname := fun sk => (map (KModSem.mn ∘ (flip KMod.get_modsem sk)) _kmds).
  Let kmds: list SMod.t := List.map KMod.transl_tgt _kmds.
  Variable umds: list Mod.t.

  Let sk_link: Sk.t := Sk.sort (fold_right Sk.add Sk.unit ((List.map SMod.sk kmds) ++ (List.map Mod.sk umds))).
  Let skenv: SkEnv.t := Sk.load_skenv sk_link.

  Let _kmss: Sk.t -> list SModSem.t := fun ske => List.map (flip SMod.get_modsem ske) kmds.
  Let _umss: Sk.t -> list ModSem.t := fun ske => List.map (flip Mod.get_modsem ske) umds.
  Let _gstb: Sk.t -> list (gname * fspec) := fun ske =>
    (flat_map (List.map (map_snd fsb_fspec) ∘ SModSem.fnsems) (_kmss ske))
      ++ (flat_map (List.map (map_snd (fun _ => KModSem.disclose_tgt fspec_trivial)) ∘ ModSem.fnsems) (_umss ske)).

  Let kmss: list SModSem.t := Eval red in (_kmss sk_link).
  Let umss: list ModSem.t := Eval red in (_umss sk_link).
  Let gstb: list (gname * fspec) := Eval red in (_gstb sk_link).

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
    | [ H: ModSem.map_snd _ _ = _ |- _ ] => unfold ModSem.map_snd in H; ss
    | [ H: map_snd _ _ = _ |- _ ] => unfold map_snd in H; ss
    | [ H: flip _ _ _ = _ |- _ ] => unfold flip in H; ss

    | [ |- context[ModL.enclose] ] => unfold ModL.enclose; try rewrite add_list_fnsems
    | [ |- In _ (flat_map _ _) ] => apply in_flat_map; esplits; et
    | [ |- In _ (List.map _ _) ] => apply in_map_iff; esplits; et
    | [ |- ModSem.map_snd _ _ = _ ] => unfold ModSem.map_snd; ss
    | [ |- map_snd _ _ = _ ] => unfold map_snd; ss
    | [ |- flip _ _ _ = _ ] => unfold flip; ss
    end
  .
  Ltac list_tac := repeat _list_tac.


  Lemma my_lemma1_aux''
        (ske: Sk.t) mr0 st0 (A: Type) (itr: itree Es A) (ctx: Σ)
        mn
        fr0 fr_trash
        (* (WF: URA.wf (ctx ⋅ mr0)) *)
        (WF: URA.wf ctx)
    :
      paco7
        (_sim_itree (fun (_: unit) '((mr_src, st_src), (mr_tgt, st_tgt)) =>
                       mr_src = ε /\ st_src = (Any.pair mr_tgt↑ st_tgt)) top2)
        bot7
        (Σ * (Σ * A))%type A
        (fun '((mr_src, st_src), fr_src) '((mr_tgt, st_tgt), fr_tgt) '(ctx, (_, r_src)) r_tgt =>
           mr_src = ε /\ st_src = (Any.pair mr_tgt↑ st_tgt) /\ r_src = r_tgt
           /\ URA.wf ctx
        )
        40%nat tt
        (ε, (Any.pair mr0↑ st0), fr_trash, (interp_hCallE_tgt mn (_gstb ske) ord_top
                                                              (massage_itr (_gstb ske) true itr fr0) ctx))
        (mr0, st0, fr0, addtau itr)
  .
  Proof.
    ginit. revert_until ske. gcofix CIH. i. ides itr.
    { steps. }
    { steps. gbase. eapply CIH; et. }
    rewrite <- bind_trigger.
    destruct e; cycle 1.
    {
      destruct s; ss.
      { destruct r0; ss.
        - resub. ired_both. steps.
          rewrite Any.pair_split. steps. gbase. eapply CIH; et.
        - resub. ired_both. resub.
          steps. gbase. eapply CIH; et.
        - resub. ired_both. steps.
          rewrite Any.pair_split. steps. rewrite Any.upcast_downcast. steps. gbase. eapply CIH; et.
        - resub. ired_both. steps. gbase. eapply CIH; et.
      }
      destruct s.
      { destruct p; ss.
        - resub. ired_both. resub. steps. rewrite Any.pair_split. steps. gbase. eapply CIH; et.
        - resub. ired_both. resub. steps. rewrite Any.pair_split. steps. gbase. eapply CIH; et.
      }
      { destruct e; ss.
        - resub. ired_both. resub.
          gstep. eapply sim_itree_tau_tgt; eauto with ord_step.
          ired_both. gstep; econs; et. i. esplits; et. steps. gbase. eapply CIH; et.
        - resub. ired_both. resub.
          gstep. eapply sim_itree_tau_tgt; eauto with ord_step.
          ired_both. gstep; econs; et. i. esplits; et. steps. gbase. eapply CIH; et.
        - resub. ired_both. resub.
          gstep. eapply sim_itree_tau_tgt; eauto with ord_step.
          ired_both. gstep; econs; et. i. esplits; et. steps. gbase. eapply CIH; et.
      }
    }
    destruct c. resub. ired_both. resub. steps. rewrite _UNWRAPU. steps.
    rename _UNWRAPU into T.
    eapply alist_find_some in T. unfold _gstb in T. rewrite in_app_iff in *. des; ss.
    - list_tac.
      des_ifs. unfold _kmss in T. list_tac. subst. unfold kmds in T0. list_tac. subst.
      ss. list_tac. des_ifs. ss.
      unfold HoareCall, discard, forge, put, checkWf. steps.
      force_l. exists (ε, ε). steps.
      force_l.
      { rewrite ! URA.unit_id. auto. }
      steps. force_l. exists ε. steps.
      force_l. exists ε. steps. force_l.
      { rewrite URA.unit_id. auto. }
      steps. force_l. exists None. steps.
      force_l. exists (args). steps.
      force_l. exists ord_top. steps.
      force_l.
      { eapply to_semantic; [|eapply URA.wf_unit]. iIntros. iPureIntro.
        esplits; et. }
      steps. force_l.
      { split; et. }
      steps. gstep. econs; et.
      { exact tt. }
      i. des_ifs. des; subst. eexists. steps.
      red in _ASSUME0. uipropall. subst.
      destruct w1. gbase. eapply CIH; et.
      eapply URA.wf_mon; et.
    - list_tac.
      des_ifs. unfold _umss in T. list_tac. subst.
      unfold HoareCall, discard, forge, put, checkWf. steps.
      force_l. exists (ε, ε). steps.
      force_l.
      { rewrite ! URA.unit_id. auto. }
      steps. force_l. exists ε. steps.
      force_l. exists ε. steps. force_l.
      { rewrite URA.unit_id. auto. }
      steps. force_l. exists None. steps.
      force_l. eexists (args). steps.
      force_l. exists ord_top. steps.
      force_l.
      { eapply to_semantic; [|eapply URA.wf_unit]. iIntros. iPureIntro. esplits; et. }
      steps. force_l.
      { split; et. }
      steps. gstep. econs; et.
      { exact tt. }
      i. des_ifs. des; subst. eexists. steps.
      red in _ASSUME0. uipropall. subst.
      destruct w1. gbase. eapply CIH; ss.
      eapply URA.wf_mon; et.
    Unshelve.
    all: try (exact Ord.O).
    all: try (exact 0%nat).
  Qed.

  Ltac r_wf H := eapply prop_ext_rev; [eapply f_equal|]; [|eapply H]; r_solve.

  Lemma my_lemma1_aux
        mn ske
        (UNKNOWN: ~In mn (frds ske))
        ktr arg mr0 st0
    :
      sim_itree (fun (_: unit) '((mr_src, st_src), (mr_tgt, st_tgt)) =>
                       mr_src = ε /\ st_src = (Any.pair mr_tgt↑ st_tgt)) top2 100%nat tt
                (ε, (Any.pair mr0↑ st0), ε, fun_to_tgt mn (_gstb ske) (massage_fsb (_gstb ske) true ktr) arg)
                (mr0, st0, ε, addtau (ktr arg))
  .
  Proof.
    Local Transparent HoareFun.
    unfold fun_to_tgt, HoareFun, discard, forge, checkWf, put, cfun.
    Local Opaque HoareFun.
    ginit. steps.
    assert (x3 = ord_top /\ exists b, x0 = Any.pair b t).
    { destruct x1; ss.
      { red in _ASSUME0. uipropall. des. uipropall. des.
        red in _ASSUME0. red in _ASSUME1. uipropall. des. subst. et. }
      { uipropall. red in _ASSUME0. uipropall. des. clarify. et. }
    }
    des; clarify. clear _ASSUME0.
    unfold massage_fun.
    rewrite Any.pair_split. steps.
    guclo lordC_spec. econs.
    { instantiate (1:=(29 + (40))%ord). rewrite <- ! OrdArith.add_from_nat; cbn. eapply OrdArith.le_from_nat. lia. }
    erewrite idK_spec with (i0:=(addtau (ktr (o, t)))).
    guclo lbindC_spec. econs.
    { instantiate (1:=tt).
      instantiate (1:=(fun '((mr_src, st_src), fr_src) '((mr_tgt, st_tgt), fr_tgt) '(ctx, (_, r_src)) r_tgt =>
                         mr_src = ε /\ st_src = (Any.pair mr_tgt↑ st_tgt) /\ r_src = r_tgt
                         /\ URA.wf ctx)).
      gfinal. right. eapply my_lemma1_aux''; et.
      eapply URA.wf_mon; et.
    }
    i. des_ifs. ss. des_ifs. ss. des; clarify. unfold idK. steps.
    force_l. eexists. force_l. eexists (_, _). steps.
    force_l.
    { instantiate (1:=ε). instantiate (1:=ε). rewrite ! URA.unit_id; ss. }
    steps. force_l. eexists.
    force_l.
    { red. destruct x1; red; uipropall. }
    steps. force_l. eexists. force_l.
    { instantiate (1:=ε). instantiate (1:=ε). rewrite URA.unit_id. auto. }
    steps.
    Unshelve. all: try exact tt.
  Qed.

  Lemma my_lemma1
        umd
        (IN: In umd umds)
    :
      ModPair.sim (SMod.to_tgt _gstb (massage_md _gstb true umd)) (addtau_md umd)
  .
  Proof.
    econs; ss.
    i. r. econs.
    { instantiate (1:=fun (_ _: unit) => True). ss. }
    { instantiate (1:=(fun (_: unit) '((mr_src, st_src), (mr_tgt, st_tgt)) =>
                       mr_src = ε /\ st_src = (Any.pair mr_tgt↑ st_tgt))). ss.
      set (ums:=Mod.get_modsem umd sk) in *.
      rewrite ! List.map_map.
      eapply Forall2_apply_Forall2.
      { refl. }
      i. subst. unfold map_snd. des_ifs.
      rr. split; ss. r. ii. destruct w. des_ifs. des; subst. ss. esplits; et. eapply my_lemma1_aux.
      { admit "ez". }
    }
    { ss. }
    { ss. }
  Qed.

  Hypothesis WFR: URA.wf (List.fold_left (⋅) (List.map (SModSem.initial_mr) kmss) ε).
  (* Hypothesis MAINM: In (SMod.main mainpre mainbody) kmds. *)

  Let kmns: Sk.t -> list mname := (List.map fst) ∘ _gstb.
  Let _kmns: list (option mname) := (None :: (List.map Some (kmns sk_link))).

  Require Import SimGlobal.

  Let prog_src := Mod.add_list (map (KMod.transl_src kmns) _kmds ++ umds).
  Let prog_mid := Mod.add_list (map (KMod.transl_src kmns) _kmds ++ map (SMod.to_src ∘ massage_md _gstb false) umds).
  Let prog_tgt := Mod.add_list (map SMod.to_src kmds ++ map (SMod.to_src ∘ massage_md _gstb true) umds).

  Lemma stb_find_iff_mid fn
    :
      ((<<SRC: alist_find fn (ModSemL.fnsems (ModL.enclose prog_mid)) = None>>) /\
       (<<TGT: alist_find fn (ModSemL.fnsems (ModL.enclose prog_tgt)) = None>>)) \/
      (exists mn ksb,
          (<<SRC: alist_find fn (ModSemL.fnsems (ModL.enclose prog_mid)) = Some (transl_all (T:=_) mn ∘ KModSem.disclose_ksb_src (kmns sk_link) ksb)>>) /\
          (<<TGT: alist_find fn (ModSemL.fnsems (ModL.enclose prog_tgt)) = Some (transl_all (T:=_) mn ∘ (fun_to_src (KModSem.disclose_ksb_tgt ksb).(fsb_body)))>>) /\
          (<<MN: List.In (Some mn) _kmns>>)) \/
      (exists mn uf,
          (<<SRC: alist_find fn (ModSemL.fnsems (ModL.enclose prog_mid)) = Some (transl_all (T:=_) mn ∘ (fun_to_src (massage_fsb (_gstb sk_link) false uf).(fsb_body)))>>) /\
          (<<TGT: alist_find fn (ModSemL.fnsems (ModL.enclose prog_tgt)) = Some (transl_all (T:=_) mn ∘ (fun_to_src (massage_fsb (_gstb sk_link) true uf).(fsb_body)))>>) /\
          (<<MN: ~ List.In (Some mn) _kmns>>)).
  Proof.
    admit "alist find".
  Qed.

  Variant my_lemma2_r1: forall R0 R1 (RR: R0 -> R1 -> Prop), Ord.t -> itree eventE R0 -> itree eventE R1 -> Prop :=
  | my_lemma2_r1_intro
      R mn (itr: itree _ R) st
      (MN: List.In (Some mn) _kmns)
    :
      my_lemma2_r1 eq 200
                   (EventsL.interp_Es (ModSemL.prog (ModL.enclose prog_mid)) (transl_all mn (KModSem.interp_kCallE_src itr)) st)
                   (EventsL.interp_Es (ModSemL.prog (ModL.enclose prog_tgt)) (transl_all mn (interp_hCallE_src (KModSem.transl_itr_tgt itr))) st)
  .

  Variant my_lemma2_r2: forall R0 R1 (RR: R0 -> R1 -> Prop), Ord.t -> itree eventE R0 -> itree eventE R1 -> Prop :=
  | my_lemma2_r2_intro
      R mn (itr: itree _ R) st r
      (MN: ~ List.In (Some mn) _kmns)
    :
      my_lemma2_r2 eq 200
                   (EventsL.interp_Es (ModSemL.prog (ModL.enclose prog_mid)) (transl_all mn (interp_hCallE_src (massage_itr (_gstb sk_link) false itr r))) st)
                   (EventsL.interp_Es (ModSemL.prog (ModL.enclose prog_tgt)) (transl_all mn (interp_hCallE_src (massage_itr (_gstb sk_link) true itr r))) st)
  .

  Let my_r := my_lemma2_r1 \6/ my_lemma2_r2.

  Ltac gsteps := HoareDef.steps.

  Lemma my_lemma2_aux
    :
      my_r <6= simg.
  Proof.
    Local Opaque _kmns in_dec.
    ginit.
    { i. eapply cpn6_wcompat; eauto with paco. }
    gcofix CIH. i. destruct PR.
    { destruct H. destruct st as [[fr mr] mp]. ides itr.
      { gsteps. }
      { gsteps. gbase. eapply CIH. left. econs. auto. }
      rewrite <- bind_trigger. destruct e.
      { resub. destruct k0. gsteps. destruct kf.
        { gsteps. exists x_tgt. gsteps. gbase. eapply CIH. left. econs. auto. }
        { gsteps. destruct mr.
          { gsteps. }
          gsteps. hexploit (stb_find_iff_mid fn). i. des.
          { rewrite SRC. rewrite TGT. gsteps. }
          { rewrite SRC. rewrite TGT. gsteps.
            unfold my_if, sumbool_to_bool. des_ifs.
            unfold fun_to_src, body_to_src. rewrite Any.pair_split. gsteps.
            rewrite Any.upcast_downcast. gsteps.
            guclo bindC_spec. econs.
            { gbase. eapply CIH. left. econs. auto. }
            i. subst. destruct vret_tgt as [[[fr0 mr0] mp0] retv].
            gsteps. destruct mr0; gsteps.
            gbase. eapply CIH. left. econs. auto.
          }
          { rewrite SRC. rewrite TGT. gsteps.
            unfold fun_to_src, body_to_src. rewrite Any.pair_split. gsteps.
            guclo bindC_spec. econs.
            { gbase. eapply CIH. right. econs. auto. }
            i. subst. destruct vret_tgt as [[[fr0 mr0] mp0] retv].
            gsteps. destruct mr0; gsteps.
            gbase. eapply CIH. left. econs. auto.
          }
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
    { destruct H. destruct st as [[fr mr] mp]. ides itr.
      { gsteps. }
      { gsteps. gbase. eapply CIH. right. econs. auto. }
      rewrite <- bind_trigger. destruct e.
      { resub. destruct c. gsteps.
        destruct (alist_find fn (_gstb sk_link)).
        2: { admit "remove function existence checking in massage". }
        gsteps. destruct mr.
        { gsteps. }
        gsteps. hexploit (stb_find_iff_mid fn). i. des.
        { rewrite SRC. rewrite TGT. gsteps. }
        { rewrite SRC. rewrite TGT. gsteps.
          unfold my_if, sumbool_to_bool. des_ifs.
          unfold fun_to_src, body_to_src. rewrite Any.pair_split. gsteps.
          rewrite Any.upcast_downcast. gsteps.
          guclo bindC_spec. econs.
          { gbase. eapply CIH. left. econs. auto. }
          i. subst. destruct vret_tgt as [[[fr0 mr0] mp0] retv].
          gsteps. destruct mr0; gsteps.
          gbase. eapply CIH. right. econs. auto.
        }
        { rewrite SRC. rewrite TGT. gsteps.
          unfold fun_to_src, body_to_src. rewrite Any.pair_split. gsteps.
          guclo bindC_spec. econs.
          { gbase. eapply CIH. right. econs. auto. }
          i. subst. destruct vret_tgt as [[[fr0 mr0] mp0] retv].
          gsteps. destruct mr0; gsteps.
          gbase. eapply CIH. right. econs. auto.
        }
      }
      destruct s.
      { resub. destruct r1.
        { gsteps. destruct (Any.split (mp mn)); gsteps.
          gbase. eapply CIH. right. econs. auto. }
        { gsteps. gbase. eapply CIH. right. econs. auto. }
        { gsteps. destruct (Any.split (mp mn)); gsteps. destruct (Any.downcast t); gsteps.
          gbase. eapply CIH. right. econs. auto. }
        { gsteps. gbase. eapply CIH. right. econs. auto. }
      }
      destruct s.
      { resub. destruct p.
        { gsteps. destruct (Any.split (mp mn)); gsteps.
          gbase. eapply CIH. right. econs. auto. }
        { gsteps. destruct (Any.split (mp mn)); gsteps.
          gbase. eapply CIH. right. econs. auto. }
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
      eapply flat_map_ext. i. ss. f_equal. f_equal.
      f_equal. admit "TODO: fix the definition".
    }
    { rewrite ! flat_map_map.
      eapply flat_map_ext. i. ss. }
  Qed.

  Lemma my_lemma2_initial_state
    :
      (ModSemL.initial_r_state (ModL.enclose prog_mid), ModSemL.initial_p_state (ModL.enclose prog_mid))
      =
      (ModSemL.initial_r_state (ModL.enclose prog_tgt), ModSemL.initial_p_state (ModL.enclose prog_tgt)).
  Proof.
    unfold ModL.enclose.
    unfold ModSemL.initial_r_state, ModSemL.initial_p_state.
    rewrite my_lemma2_initial_mrs. auto.
  Qed.

  Lemma my_lemma2 main_arg:
    Beh.of_program (ModL.compile_arg (Mod.add_list (List.map SMod.to_src kmds ++ List.map (SMod.to_src ∘ massage_md _gstb true) umds)) (Any.pair true↑ main_arg)) <1=
    Beh.of_program (ModL.compile_arg (Mod.add_list (List.map (KMod.transl_src kmns) _kmds ++ List.map (SMod.to_src ∘ massage_md _gstb false) umds)) main_arg).
  Proof.
    eapply adequacy_global_itree.
    exists (200)%ord.
    ginit.
    { eapply cpn6_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr, ModSemL.initial_itr_arg.
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
      rewrite Any.upcast_downcast. gsteps.
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
      ModPair.sim (addtau_md md) (SMod.to_src (massage_md _gstb false md)).
  Proof.
    econs; ss. i.
    eapply ModSemPair.mk with (wf:=fun (_: unit) '((mr_src, mp_src), (mr_tgt, mp_tgt)) =>
                                     mp_tgt = Any.pair mr_src↑ mp_src) (le:=top2).
    { ss. }
    { ss. rewrite ! map_map.
      eapply Forall2_apply_Forall2.
      { refl. }
      i. subst. destruct b as [fn f]. ss. econs.
      { ss. }
      ii. subst.
      destruct mrs_src as [mr_src mp_src]. destruct mrs_tgt as [mr_tgt mp_tgt]. subst.
      exists 100. ginit. unfold fun_to_src, body_to_src. ss. destruct y.
      rewrite interp_src_bind.
      guclo @lordC_spec. econs.
      { instantiate (1:=(50+50)%ord). rewrite <- OrdArith.add_from_nat. refl. }
      unfold addtau_ktr. erewrite (idK_spec (addtau (f (o, t)))).
      guclo @lbindC_spec. econs.
      { instantiate (1:=tt).
        instantiate (1:=fun '(mr_src, mp_src, fr_src) '(mr_tgt, mp_tgt, fr_tgt) ret_src ret_tgt => mp_tgt = Any.pair mr_src↑ mp_src /\ snd ret_tgt = ret_src).
        generalize (f (o, t)). generalize (@URA.unit (GRA.to_URA Σ)) at 1 3.
        revert mr_src mp_src mr_tgt.
        gcofix CIH. i. ides i.
        { steps. }
        { steps. gbase. eapply CIH. }
        rewrite <- bind_trigger. destruct e.
        { resub. destruct c0. steps. gstep. econs; et. i.
          exists 100. steps. gbase. destruct w1. eapply CIH.
        }
        destruct s.
        { resub. destruct r0.
          { ired_both. force_r. steps.
            { instantiate (1:=100). shelve. }
            rewrite Any.pair_split in *. clarify.
            gbase. eapply CIH.
          }
          { ired_both. steps. gbase. eapply CIH. }
          { ired_both. force_r. steps.
            { instantiate (1:=100). shelve. }
            rewrite Any.pair_split in *. clarify.
            rewrite Any.upcast_downcast in *. clarify.
            gbase. eapply CIH.
          }
          { ired_both. steps. gbase. eapply CIH. }
        }
        destruct s.
        { resub. destruct p.
          { ired_both. force_r. steps.
            { instantiate (1:=100). shelve. }
            steps. rewrite Any.pair_split in *. clarify.
            gbase. eapply CIH. }
          { ired_both. force_r. steps.
            { instantiate (1:=100). shelve. }
            rewrite Any.pair_split in *. clarify.
            gbase. eapply CIH.
          }
        }
        { resub. destruct e.
          { ired_both. resub. force_r. i. steps. force_l. exists x. steps.
            gbase. eapply CIH. }
          { ired_both. resub. force_l. force_l. i.
            force_r. exists x. steps. gbase. eapply CIH. }
          { ired_both. resub. steps. gstep. econs. i. esplits.
            steps. gbase. eapply CIH.
          }
        }
      }
      { i. unfold idK.
        destruct vret_tgt. ss. destruct st_src1, st_tgt1. destruct p, p0.
        ss. des. clarify. steps.
      }
    }
    { ss. }
    { exists tt. ss. }
    Unshelve. all: try (exact 0).
    { rewrite <- ! OrdArith.add_from_nat. eapply OrdArith.lt_from_nat. lia. }
    { rewrite <- ! OrdArith.add_from_nat. eapply OrdArith.lt_from_nat. lia. }
    { rewrite <- ! OrdArith.add_from_nat. eapply OrdArith.lt_from_nat. lia. }
    { rewrite <- ! OrdArith.add_from_nat. eapply OrdArith.lt_from_nat. lia. }
  Qed.

  Lemma my_lemma3:
    Beh.of_program (ModL.compile (Mod.add_list (List.map (KMod.transl_src kmns) _kmds ++ List.map (SMod.to_src ∘ massage_md _gstb false) umds))) <1=
    Beh.of_program (ModL.compile (Mod.add_list (List.map (KMod.transl_src kmns) _kmds ++ umds))).
  Proof.
    eapply refines_close.
    transitivity (Mod.add_list (map (KMod.transl_src kmns) _kmds ++ map addtau_md umds)).
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

  Theorem adequacy_open:
    refines_closed (Mod.add_list (List.map (SMod.to_tgt _gstb) kmds ++ umds))
                   (Mod.add_list (List.map (KMod.transl_src kmns) _kmds ++ umds))
  .
  Proof.
    transitivity (Mod.add_list (List.map (SMod.to_tgt _gstb) kmds ++ List.map (SMod.to_tgt _gstb ∘ massage_md _gstb true) umds)).
    { eapply refines_close.
      transitivity (Mod.add_list (map (SMod.to_tgt _gstb) kmds ++ map addtau_md umds)).
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
    rewrite <- (map_map (massage_md _gstb true)). rewrite <- map_app.
    eapply adequacy_type_arg.
    { i. admit "main". }
    match goal with
    | H: Beh.of_program ?p0 x0 |- Beh.of_program ?p1 x0 => replace p1 with p0
    end.
    { auto. }
    rewrite ModL.compile_compile_arg_nil. f_equal. f_equal.
    match goal with
    | |- _ = map (SMod.to_tgt ?gstb) _ => assert (_gstb = gstb)
    end.
    { unfold _gstb. extensionality sk.
      rewrite map_app. rewrite flat_map_app. rewrite map_app.
      f_equal.
      { unfold _kmss. rewrite ! map_flat_map.
        rewrite ! flat_map_map. f_equal. }
      { unfold _umss. rewrite ! map_flat_map.
        rewrite ! flat_map_map. f_equal. extensionality md.
        ss. rewrite ! map_map. f_equal.
        extensionality x. destruct x. ss.
      }
    }
    rewrite <- H. rewrite map_app. rewrite map_map. ss.
  Qed.

End ADQ.
