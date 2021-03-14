Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import SimModSem.

Require Import HTactics.

From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.





Section PROOF.

  Context `{Σ: GRA.t}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).

  Variant fspec_weaker (fsp_src fsp_tgt: fspec): Prop :=
  | fspec_weaker_intro
      mn X_src X_tgt AA AR P_src P_tgt Q_src Q_tgt
      (FSPEC0: fsp_src = @mk _ mn X_src AA AR P_src Q_src)
      (FSPEC1: fsp_tgt = @mk _ mn X_tgt AA AR P_tgt Q_tgt)
      (WEAK: forall (x_src: X_src),
          exists (x_tgt: X_tgt),
            (<<PRE: P_tgt x_tgt <4= P_src x_src>>) /\
            (<<POST: Q_src x_src <3= Q_tgt x_tgt>>))
  .

  Variable stb_src stb_tgt: list (gname * fspec).
  Hypothesis stb_stronger:
    forall fn fn_tgt fsp_tgt (FINDTGT: List.find (fun '(_fn, _) => dec fn _fn) stb_tgt = Some (fn_tgt, fsp_tgt)),
    exists fn_src fsp_src,
      (<<FINDSRC: List.find (fun '(_fn, _) => dec fn _fn) stb_src = Some (fn_src, fsp_src)>>) /\
      (<<WEAKER: fspec_weaker fsp_tgt fsp_src>>)
  .

  Variable fn: gname.

  Variable fsp_src fsp_tgt: fspec.
  Hypothesis fsp_weaker: fspec_weaker fsp_src fsp_tgt.

  Variable body_src: fsp_src.(AA) -> itree (hCallE +' pE +' eventE) fsp_src.(AR).
  Variable body_tgt: fsp_tgt.(AA) -> itree (hCallE +' pE +' eventE) fsp_tgt.(AR).
  Hypothesis body_eq: JMeq body_src body_tgt.

  Lemma weakening_fn:
    sim_fsem (fun '(w_src, w_tgt) => w_src = w_tgt)
             (fun_to_tgt stb_src fn (mk_specbody fsp_src body_src))
             (fun_to_tgt stb_tgt fn (mk_specbody fsp_tgt body_tgt)).
  Proof.
  Admitted.
    (* inv fsp_weaker. ss. subst. ii. subst. exists 0. *)
    (* unfold fun_to_tgt. ss. repeat rewrite HoareFun_parse. *)

End PROOF.
