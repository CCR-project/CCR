Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef OpenDef STB SimModSem.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import ProofMode Invariant.
Require Import HTactics2 HSim2.
Require Export ISim2 IProp IPM.
From iris.bi Require Import bi telescopes.
From iris.proofmode Require Import base environments coq_tactics.



Ltac get_fresh_string :=
  match goal with
  | |- context["A"] =>
      match goal with
      | |- context["A0"] =>
          match goal with
          | |- context["A1"] =>
              match goal with
              | |- context["A2"] =>
                  match goal with
                  | |- context["A3"] =>
                      match goal with
                      | |- context["A4"] =>
                          match goal with
                          | |- context["A5"] =>
                              match goal with
                              | |- context["A6"] =>
                                  match goal with
                                  | |- context["A7"] =>
                                      match goal with
                                      | |- context["A8"] =>
                                          match goal with
                                          | |- context["A9"] =>
                                              match goal with
                                              | |- context["A10"] =>
                                                  match goal with
                                                  | |- context["A11"] =>
                                                      match goal with
                                                      | |- context["A12"] => fail 12
                                                      | _ => constr:("A12")
                                                      end
                                                  | _ => constr:("A11")
                                                  end
                                              | _ => constr:("A10")
                                              end
                                          | _ => constr:("A9")
                                          end
                                      | _ => constr:("A8")
                                      end
                                  | _ => constr:("A7")
                                  end
                              | _ => constr:("A6")
                              end
                          | _ => constr:("A5")
                          end
                      | _ => constr:("A4")
                      end
                  | _ => constr:("A3")
                  end
              | _ => constr:("A2")
              end
          | _ => constr:("A1")
          end
      | _ => constr:("A0")
      end
  | _ => constr:("A")
  end
.
(* Ltac iDes := *)
(*   repeat multimatch goal with *)
(*          | |- context[@environments.Esnoc _ _ (INamed ?namm) ?ip] => *)
(*            match ip with *)
(*            | @bi_or _ _ _ => *)
(*              let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ "|" +:+ namm +:+ "]")) in *)
(*              iDestruct namm as pat *)
(*            | @bi_pure _ _ => iDestruct namm as "%" *)
(*            | @iNW _ ?newnamm _ => iEval (unfold iNW) in namm; iRename namm into newnamm *)
(*            | @bi_sep _ _ _ => *)
(*              let f := get_fresh_string in *)
(*              let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ " " +:+ f +:+ "]")) in *)
(*              iDestruct namm as pat *)
(*            | @bi_exist _ _ (fun x => _) => *)
(*              let x := fresh x in *)
(*              iDestruct namm as (x) namm *)
(*            end *)
(*          end *)
(* . *)
Ltac iCombineAll :=
  repeat multimatch goal with
         | |- context[@environments.Esnoc _ (@environments.Esnoc _ _ (INamed ?nam1) _) (INamed ?nam2) _] =>
           iCombine nam1 nam2 as nam1
         end
.
Ltac xtra := iCombineAll; iAssumption.














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
  let ident := first_fresh name constr:(0%nat) in constr:(ident)
  (* let l := constr:(or_else (last (list_ascii_of_string name)) zero) in *)
  (* match constr:(is_nat l) with *)
  (* | Some ?n => let ident := first_fresh name n in constr:(ident) *)
  (* | _ => let ident := first_fresh name constr:(0%nat) in constr:(ident) *)
  (* end *)
.

Ltac iDes' l :=
  match l with
  | Enil => idtac
  | Esnoc ?tl (IAnon ?x) ?P =>
      match goal with
      | |- envs_entails ?Δ _ => let name := get_fresh_string in iRename (IAnon x) into name
      end
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
              let ident' := get_fresh_string in
              let str := constr:(("[" ++ ident ++ " " ++ ident' ++ "]")%string) in
              iDestruct ident as str
          end
      | (⌜_⌝)%I => iDestruct ident as "[%]"
      | ({{?H: _}})%I => iEval ltac:(unfold iNW) in ident; iRename ident into H
      | (_ ∨ _)%I =>
          let str := constr:(("[" ++ ident ++ "|" ++ ident ++ "]")%string) in
          iDestruct ident as str
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
             | |- envs_entails ?Δ _ => let name := get_fresh_string in iRename (IAnon x) into name
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

Goal forall {PROP : bi} (P Q: PROP) R, bi_entails True ((P ∗ Q ∗ ⌜R⌝ ∨ ⌜False⌝) -* ⌜True⌝).
  i. iIntros. iDes.
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
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
      let name := fresh "G" in
      cut (P); [intros name; iApply isim_assume_tgt; iSplitR; [iPureIntro; exact name|]|]; cycle 1
  end
.

Ltac step0 :=
  match goal with
  (** src **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
      let name := fresh "y" in
      iApply isim_unwrapU_src; iIntros (name) "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
      iApply isim_assume_src; iIntros "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, tau;; _) (_, _)) ] =>
      iApply isim_tau_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (PPut _) >>= _) (_, _)) ] =>
      iApply isim_pput_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (PGet) >>= _) (_, _)) ] =>
      iApply isim_pget_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) (_, _)) ] =>
      let name := fresh "y" in
      iApply isim_take_src; iIntros (name)

  (** tgt **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
      let name := fresh "y" in
      iApply isim_unwrapN_tgt; iIntros (name) "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
      iApply isim_guarantee_tgt; iIntros "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, _) (_, tau;; _)) ] =>
      iApply isim_tau_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (PPut _) >>= _)) ] =>
      iApply isim_pput_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (PGet) >>= _)) ] =>
      iApply isim_pget_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Choose _) >>= _)) ] =>
      let name := fresh "y" in
      iApply isim_choose_tgt; iIntros (name)

  (** src-apc **)
  (* | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, ;;; _) (_, _)) ] => *)
  (*     iApply isim_apc; iExists (Some (100: Ord.t)) *)
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
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (Call ?x0 ?y0) >>= _)
                                           (_, trigger (Call ?x1 ?y1) >>= _)) ] =>
      iApply isim_call_impure; [autounfold with stb; autorewrite with stb; refl|
                                 autounfold with stb; autorewrite with stb; refl|]
      (* match goal with *)
      (* | [ STBINCL: stb_incl _ _ |- _ ] => *)
      (*     iApply isim_call_impure; [eapply fn_has_spec_in_stb; [eapply STBINCL; stb_tac; ss|ss|ss]|] *)
      (* end *)

  (** ret **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _)) ] =>
      iApply isim_ret
  end.

Ltac step1 :=
  match goal with
  (** pure call **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?x0 ?y0) >>= _)) ] =>
      iApply isim_call_pure; [autounfold with stb; autorewrite with stb; refl|
                               autounfold with stb; autorewrite with stb; refl|]
      (* match goal with *)
      (* | [ STBINCL: stb_incl _ _ |- _ ] => *)
      (*     iApply isim_call_pure; [eapply fn_has_spec_in_stb; [eapply STBINCL; stb_tac; ss|ss|ss]|oauto|] *)
      (* end *)
  end
.

Ltac des_pairs :=
  repeat match goal with
         | [H: context[let (_, _) := ?x in _] |- _] =>
             let n0 := fresh x in let n1 := fresh x in destruct x as [n0 n1]
         | |- context[let (_, _) := ?x in _] =>
             let n0 := fresh x in let n1 := fresh x in destruct x as [n0 n1]
         end.

Ltac steps :=
  repeat (repeat (prep; try step0; simpl; des_pairs); try step1).

Goal let (a, b) := (1, 0) in a = 1. simpl. Abort.
Goal forall (x: nat * nat), let (a, b) := x in a = 1. i. des_pairs. Abort.
Goal forall (x: nat * nat), (let (a, b) := x in a = 1) -> False. i. des_pairs. Abort.

Ltac des_eqs :=
  repeat match goal with
         | |- context[?x ?[ ?t ] ?y] =>
             let name := fresh "EQ" in
             destruct (x ?[ t ] y) eqn:name;
             [apply rel_dec_correct in name; clarify|clear name]
         | [H: context[?x ?[ ?t ] ?y] |- _] =>
             let name := fresh "EQ" in
             destruct (x ?[ t ] y) eqn:name;
             [apply rel_dec_correct in name; try (injection H; clear H; i); clarify|clear name]
         end.

Ltac startproof :=
  apply isim_fun_to_tgt;
  [typeclasses eauto
  |autounfold with stb in *; autorewrite with stb in *; cbn; i; des_eqs; econs;
   cbn; i; des_ifs; iIntros; iDes; des; eauto
  |cbn; autounfold with stb in *; autorewrite with stb in *;
   match goal with
   | |- context[_ = Some ?x] =>
       repeat multimatch goal with
              | |- context[(?y, ?z)] => match z with | x => exists y end
              end
   end;
   refl
  |cbn; autounfold with stb in *; autorewrite with stb in *; ii; ss; des_eqs;
   match goal with
   | [H: is_possibly_pure _ |- _] => rr in H; des; ss
   end
  |cbn; unfold cfunN, cfunU, ccallN, ccallU; cbn
  ].
