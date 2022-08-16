Require Import Echo0 Echo1 HoareDef SimModSem.
Require Import Stack3A.
Require Import Coqlib.
Require Import ImpPrelude.
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
Require Import OpenDef STB.
Require Import HTactics ProofMode HSim IProofMode.

Set Implicit Arguments.

Local Open Scope nat_scope.






From iris.bi Require Export bi telescopes.
From iris.proofmode Require Import base environments coq_tactics.



(*** copied & modified from DiaFrame ***)
Ltac fresh_name name Δ := 
  let rec first_fresh name num :=
    (let base := eval cbv in (match num with | 0 => name | _ => append name (pretty.pretty_nat num) end) in
       let name_in_env := eval cbv in (existsb (fun i => ident_beq i base) (envs_dom Δ)) in
         match constr:(name_in_env) with
         | true => 
             let new_num := eval cbv in (Nat.succ num) in
               first_fresh name new_num
         | false => base
         end)
  in
  (* let ident := first_fresh name constr:(0%nat) in constr:(ident) *)
  let l := constr:(or_else (last (list_ascii_of_string name)) zero) in
  match constr:(is_nat l) with
  | Some ?n => let ident := first_fresh name n in constr:(ident)
  | _ => let ident := first_fresh name constr:(0%nat) in constr:(ident)
  end
.

Ltac iDes' l :=
  match l with
  | Enil => idtac
  | Esnoc ?tl (INamed ?ident) ?P =>
      match P with
      | (∃ x, _)%I =>
          let name := fresh x in
          eapply tac_exist_destruct with (i:=ident) (j:=ident); [reduction.pm_reflexivity|iSolveTC|cbn];
          intro name
      (*** TODO FIXME: below does not work ***)
      (* let name := fresh x in *)
      (* let str := constr:(("[" ++ ident ++ "]")%string) in *)
      (* iDestruct ident as (name) str *)
      | (⌜_⌝ ∗ _)%I =>
          let str := constr:(("[% " ++ ident ++ "]")%string) in
          iDestruct ident as str
      | (⌜_⌝ ∧ _)%I =>
          let str := constr:(("[% " ++ ident ++ "]")%string) in
          iDestruct ident as str
      | (_ ∗ ⌜_⌝)%I =>
          let str := constr:(("[" ++ ident ++ " %]")%string) in
          iDestruct ident as str
      | (_ ∧ ⌜_⌝)%I =>
          let str := constr:(("[" ++ ident ++ " %]")%string) in
          iDestruct ident as str
      | (_ ∗ _)%I =>
          match goal with
          | |- envs_entails ?Δ _ =>
              let ident' := fresh_name ident Δ in
              let str := constr:(("[" ++ ident ++ " " ++ ident' ++ "]")%string) in
              iDestruct ident as str
          end
      | (⌜_⌝)%I => iDestruct ident as "[%]"
      | _ => idtac
      end;
      iDes' tl
  end
.

Ltac iDes :=
  repeat match goal with
         | |- envs_entails (Envs _ ?l _) _ => iDes' l
         end
.

Ltac iName :=
  repeat match goal with
         | |- context[Esnoc _ (IAnon ?x) _] =>
             match goal with
             | |- envs_entails ?Δ _ => let name := fresh_name "H" Δ in iRename (IAnon x) into name
             end
         end
.

(* Ltac iIntroall := *)
(*   repeat match goal with *)
(*          | |- envs_entails ?Δ (∀ x, _) => let name := fresh x in idtac name; iIntros (name) *)
(*          | |- envs_entails ?Δ _ => let name := fresh_name "H" Δ in iIntros name *)
(*          | |- _ => iIntros "H" *)
(*          end *)
(* . *)

Goal forall {PROP : bi} (P Q: PROP) R, bi_entails True ((P ∗ Q ∗ ⌜R⌝) -* ⌜True⌝).
  i. iIntros. iName. iDes.
Abort.

Ltac ired_l := try Red.prw ltac:(IRed._red_gen) 1 2 1 0.
Ltac ired_r := try Red.prw ltac:(IRed._red_gen) 1 1 1 0.
Ltac ired_both := ired_l; ired_r.
Ltac prep := cbn; ired_both.

Ltac force_l :=
  prep;
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
      (* let tvar := fresh "tmp" in *)
      (* let thyp := fresh "TMP" in *)
      (* remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar; *)
      (* let name := fresh "G" in *)
      (* destruct (ox) eqn:name; [|exfalso]; cycle 1 *)
      idtac
      (* let name := fresh "y" in *)
      (* iApply isim_unwrapN_src; iIntros (name) "%"; *)
      (* match goal with *)
      (* | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in * *)
      (* end *)
  end
.

Ltac force_r :=
  prep;
  (* match goal with *)
  (* | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] => *)
  (*   let tvar := fresh "tmp" in *)
  (*   let thyp := fresh "TMP" in *)
  (*   remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar; *)
  (*   let name := fresh "_UNWRAPU" in *)
  (*   destruct (ox) eqn:name; [|exfalso]; cycle 1 *)
  (* | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] => *)
  (*   let tvar := fresh "tmp" in *)
  (*   let thyp := fresh "TMP" in *)
  (*   remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar; *)
  (*   let name := fresh "_ASSUME" in *)
  (*   destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_take_tgt; [exists name]|contradict name]; cycle 1 *)

  (* | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] => *)
  (*   seal i_src; apply sim_itreeC_spec; econs; unseal i_src *)
  (* end *)
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
      (* let name := fresh "y" in *)
      (* iApply isim_unwrapN_tgt; iIntros (name) "%"; *)
      (* match goal with *)
      (* | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in * *)
      (* end *)
      idtac
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
      let name := fresh "G" in
      cut (P); [intros name; iApply isim_assume_tgt; iSplitR; [iPureIntro; exact name|]|]; cycle 1
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, tau;; _)) ] =>
      iApply isim_tau_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (PPut _) >>= _)) ] =>
      iApply isim_pput_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (PGet _) >>= _)) ] =>
      iApply isim_pget_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (Choose _) >>= _)) ] =>
      let name := fresh "y" in
      iApply isim_choose_tgt; iIntros (name)
  end
.

Ltac _step :=
  match goal with
  (** src **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
      let name := fresh "y" in
      iApply isim_unwrapU_src; iIntros (name) "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
      iApply isim_assume_src; iIntros "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, tau;; _) (_, _)) ] =>
      iApply isim_tau_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (PPut _) >>= _) (_, _)) ] =>
      iApply isim_pput_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (PGet _) >>= _) (_, _)) ] =>
      iApply isim_pget_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) (_, _)) ] =>
      let name := fresh "y" in
      iApply isim_take_src; iIntros (name)

  (** tgt **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
      let name := fresh "y" in
      iApply isim_unwrapN_tgt; iIntros (name) "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
      iApply isim_guarantee_tgt; iIntros "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, tau;; _)) ] =>
      iApply isim_tau_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (PPut _) >>= _)) ] =>
      iApply isim_pput_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (PGet _) >>= _)) ] =>
      iApply isim_pget_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (Choose _) >>= _)) ] =>
      let name := fresh "y" in
      iApply isim_choose_tgt; iIntros (name)

  (** src-apc **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, ;;; _) (_, _)) ] =>
      iApply isim_apc; iExists (Some (100: Ord.t))
  (*** HEURISTIC: using 100 here is a heuristic. It makes sense only if there is no loop and only recursion.
       We can make a loop->recursion translator.
       People already annotate loop invariants, so such an additional function
       and the necessity for its specification is okay.
   ***)

  (*** HEURISTIC: If the calls are same in both sides, try impure call and try pure call otherwise.
I think this is complete technique; if the function was meant to be a pure call,
then we can use next APC to match it.
Specifically, the following examples are okay:
call X; call Y
>=
call X; call Y; call X
or
call Y; call X
>=
call X; call Y; call X
   ***)
  (** impure call **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (Call ?x0 ?y0) >>= _)
                                           (_, trigger (Call ?x1 ?y1) >>= _)) ] =>
      match goal with
      | [ STBINCL: stb_incl _ _ |- _ ] =>
          iApply isim_call_impure; [eapply fn_has_spec_in_stb; [eapply STBINCL; stb_tac; ss|ss|ss]|]
      end
  (** pure call **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?x0 ?y0) >>= _)) ] =>
      match goal with
      | [ STBINCL: stb_incl _ _ |- _ ] =>
          iApply isim_call_pure; [eapply fn_has_spec_in_stb; [eapply STBINCL; stb_tac; ss|ss|ss]|oauto|]
      end

  (** ret **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _)) ] =>
      iApply isim_ret
  end.

Ltac steps :=
  repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) simpl (* ; des_ifs_safe *)).


Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    @mk_wf _ unit
           (fun _ _ _ => ⌜True⌝%I)
  .

  (*** TODO: remove this later ***)
  Definition ClientStb: list gname.
    eapply (Seal.sealing "stb").
    let x := constr:(["getint"; "putint"]) in
    let y := eval cbn in x in
    eapply y.
  Defined.
  (* Global Opaque ClientStb. *)
  Hint Unfold ClientStb: stb.

  Variable global_stb: gname -> option fspec.
  Hypothesis STBINCL: stb_incl (to_stb_context ClientStb (EchoStb ++ StackStb)) global_stb.

  Let top2_PreOrder: @PreOrder unit top2.
  Proof. econs; eauto. Qed.
  Local Existing Instance top2_PreOrder.

  Local Opaque dec.

  Theorem sim_modsem: ModSemPair.sim (Echo1.EchoSem global_stb) (Echo0.EchoSem).
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    { esplits. econs; ss.
      - eapply to_semantic. iIntros "H". ss.
    }
    econs; ss.
    { econs; ss. apply isim_fun_to_tgt_open_trivial; auto.
      unfold Echo0.echo_body, echo_body, cfunN, cfunU, ccallN, ccallU.
      i.
      match goal with
      | |- envs_entails ?Δ _ => let n := fresh_name "INV" Δ in iIntros n
      | _ => iIntros "INV"
      end.
      steps.
      iSplitL "INV"; auto.
      iIntros (st_src0 st_tgt0 ret_src ret_tgt) "[INV POST]". iDes.
      subst.
      steps.
      iSplitL.
      { iSplitL "INV"; auto. }
      iIntros (st_src1 st_tgt1 ret_src ret_tgt) "INV POST".
      iDes. des; clarify.
      steps.
      iSplitL.
      { iSplitL "INV"; auto. }
      iIntros (st_src2 st_tgt2 ret_src ret_tgt) "INV POST".
      iDes. des; clarify.
      steps.
      iSplit; auto.
    }
    econs; ss.
    { econs; ss. apply isim_fun_to_tgt_open; auto.
      2:{ unfold Echo0.input_body, input_body, cfunU, ccallU, ccallN. ss.
          i. iIntros "H". iApply isim_triggerUB_src_trigger. auto. }
      unfold Echo0.input_body, input_body, cfunU, ccallU, ccallN. ss.
      i. iIntros "[INV POST]".
      iDes. des; clarify.
      steps.
      iSplitL "INV"; auto.
      iIntros (? ? ? ?) "INV %". subst.
      steps.
      destruct y; ss; clarify.
      force_r; ss.
      des_ifs.
      { steps. iSplitL "INV"; auto. }
      steps.
      { instantiate (1:=(_, _, _)). ss. }
      { ss. }
      ss.
      iSplitR ""; auto. iIntros (? ? ? ?) "[INV [[OWN %] %]]". subst.
      steps.
      iSplitR ""; auto.
      { iSplitL "INV"; eauto. iSplits; eauto. }
      iIntros (? ? ? ?) "INV POST".
      iDestruct "POST" as (stk1) "[% [OWN %]]". des; clarify.
      steps.
      iSplitL "INV"; auto.
    }
    econs; ss.
    { econs; ss. apply isim_fun_to_tgt_open; auto.
      2:{ unfold Echo0.input_body, input_body, cfunU, ccallU, ccallN. ss.
          i. iIntros "H". iApply isim_triggerUB_src_trigger. auto. }
      unfold Echo0.output_body, output_body, cfunU, ccallU, ccallN. ss.
      i. iIntros "[INV POST]".
      iDestruct "POST" as (? ?) "[% [POST %]]". des; clarify.
      steps.
      { instantiate (1:=(_, _)). ss. }
      { ss. }
      simpl. iSplitR ""; auto.
      iIntros (? ? ? ?) "[INV [POST %]]". subst.
      destruct stk0; ss.
      { iDestruct "POST" as "[% OWN]". subst.
        steps. force_r; ss.
        des_ifs_safe. steps. iSplitL "INV"; auto.
      }
      iDestruct "POST" as "[% OWN]". subst.
      steps. inv H1. des; ss. force_r; ss. steps.
      des_ifs. steps.
      iSplitL "INV".
      { iSplitL "INV"; auto. }
      iIntros (st_src1 st_tgt1 ret_src ret_tgt) "INV %". subst.
      steps.
      iSplitL "INV OWN".
      { iSplitL "INV"; auto. }
      iIntros (? ? ? ?) "INV POST".
      iDestruct "POST" as (stk1) "[% [OWN %]]". des; clarify.
      steps. iSplitL "INV"; auto.
    }
    Unshelve. all: ss.
  Qed.

End SIMMODSEM.
Hint Unfold ClientStb: stb.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Variable global_stb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk, stb_incl (to_stb_context ClientStb (EchoStb ++ StackStb)) (global_stb sk).

  Theorem correct: refines2 [Echo0.Echo] [Echo1.Echo global_stb].
  Proof.
    eapply adequacy_local2. econs; ss.
    { ii. eapply sim_modsem; ss. }
  Qed.

End SIMMOD.
