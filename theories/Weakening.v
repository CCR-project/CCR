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


(*   Variant bindR (r s:  *)

(*           (r s: forall S (SS: S -> S -> Prop), Ordinal.t -> (itree eventE S) -> (itree eventE S) -> Prop): *)
(*     forall S (SS: S -> S -> Prop), Ordinal.t -> (itree eventE S) -> (itree eventE S) -> Prop := *)
(*   | bindR_intro *)
(*       o0 o1 *)

(*       R RR *)
(*       (i_src i_tgt: itree eventE R) *)
(*       (SIM: r _ RR o0 i_src i_tgt) *)

(*       S SS *)
(*       (k_src k_tgt: ktree eventE R S) *)
(*       (SIMK: forall vret_src vret_tgt (SIM: RR vret_src vret_tgt), s _ SS o1 (k_src vret_src) (k_tgt vret_tgt)) *)
(*     : *)
(*       bindR r s SS (Ordinal.add o1 o0) (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt) *)
(*   . *)

(* _sim_itree *)

(* _sim_itree *)
(*      : (FMapAList.alist string (Σ * Any.t) * FMapAList.alist string (Σ * Any.t) -> *)
(*         Prop) -> *)
(*        (nat -> *)
(*         Relation_Definitions.relation *)
(*           (FMapAList.alist string (Σ * Any.t) * Σ * itree Es Any.t)) -> *)
(*        nat -> *)
(*        Relation_Definitions.relation *)
(*          (FMapAList.alist string (Σ * Any.t) * Σ * itree Es Any.t) *)


(* Hint Constructors bindR: core. *)

(* Lemma bindR_mon *)
(*       r1 r2 s1 s2 *)
(*       (LEr: r1 <5= r2) (LEs: s1 <5= s2) *)
(*   : *)
(*     bindR r1 s1 <5= bindR r2 s2 *)
(* . *)
(* Proof. ii. destruct PR; econs; et. Qed. *)

(* Definition bindC r := bindR r r. *)
(* Hint Unfold bindC: core. *)

(* Lemma bindC_wrespectful: wrespectful5 (_simg) bindC. *)
(* Proof. *)
(*   econstructor; repeat intro. *)
(*   { eapply bindR_mon; eauto. } *)
(*   rename l into llll. *)
(*   eapply bindR_mon in PR; cycle 1. *)
(*   { eapply GF. } *)
(*   { i. eapply PR0. } *)
(*   inv PR. csc. inv SIM. *)
(*   + irw. *)
(*     exploit SIMK; eauto. i. *)
(*     eapply simg_mon_ord. *)
(*     { instantiate (1:=o1). eapply Ordinal.add_base_l. } *)
(*     eapply simg_mon; eauto with paco. *)
(*   + rewrite ! bind_bind. econs; eauto. ii. *)
(*     { econs 2; eauto with paco. econs; eauto with paco. } *)


(*   + irw. econs; eauto. *)
(*     (* { eapply Ordinal.add_le_r; et. } *) *)
(*     { econs 2; eauto with paco. econs; eauto with paco. } *)
(*   + rewrite ! bind_tau. econs; eauto. *)
(*     { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. } *)
(*     econs 2; eauto with paco. econs; eauto with paco. *)
(*   + irw. econs; eauto. *)
(*     { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. } *)
(*     econs 2; eauto with paco. econs; eauto with paco. *)


(*   + rewrite ! bind_bind. econs; eauto. *)
(*     (* { eapply Ordinal.add_le_r; et. } *) *)
(*     { ii. spc SIM0. des. esplits; et. econs 2; eauto with paco. econs; eauto with paco. } *)
(*   + rewrite ! bind_bind. econs; eauto. *)
(*     { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. } *)
(*     des. esplits; et. econs 2; eauto with paco. econs; eauto with paco. *)
(*   + rewrite ! bind_bind. econs; eauto. *)
(*     { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. } *)
(*     des. esplits; et. econs 2; eauto with paco. econs; eauto with paco. *)

(*   + rewrite ! bind_bind. econs; eauto. *)
(*     (* { eapply Ordinal.add_le_r; et. } *) *)
(*     { ii. spc SIM0. des. esplits; et. econs 2; eauto with paco. econs; eauto with paco. } *)
(*   + rewrite ! bind_bind. econs; eauto. *)
(*     { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. } *)
(*     des. esplits; et. econs 2; eauto with paco. econs; eauto with paco. *)
(*   + rewrite ! bind_bind. econs; eauto. *)
(*     { instantiate (1:= Ordinal.add o1 i1). eapply Ordinal.add_lt_r; et. } *)
(*     des. esplits; et. econs 2; eauto with paco. econs; eauto with paco. *)
(* Qed. *)


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
    inv fsp_weaker. ss. subst. ii. subst. exists 0.
    unfold fun_to_tgt. ss. repeat rewrite HoareFun_parse.

    ginit.

    ii. subst. exists 0. unfold funOt




    (mk_specbody fsp_src body_tgt))


  (AR fsb_fspe)c

    :=


  fspecbody

  Variable body: AA fsb_fspec -> itree (hCallE +' pE +' eventE) (AR fsb_fspec).

  sim_fsem




         forall fn x (FINDSRC: List.find (fun '(_fn, _) => dec fn _fn) stb_src = Some (fn_src, fsp_src))
      exists fn_tgt fsp_tgt,
        (<<FINDTGT: List.find (fun '(_fn, _) => dec fn _fn) stb_tgt = x.

  Lemma sim_fnsem_wf fn



  Definition Fsbtb: list (string * fspecbody) := [("f", mk_specbody f_spec (fun _ => trigger (Choose _)))].

  Definition FSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt GlobalStb fn body)) Fsbtb;
    ModSem.initial_mrs := [("F", (ε, tt↑))];
  |}
  .

  Record fspecbody (Σ : GRA.t) : Type := mk_specbody
  { fsb_fspec : fspec;
    fsb_body : AA fsb_fspec -> itree (hCallE +' pE +' eventE) (AR fsb_fspec) }


        fun_to_tgt GlobalStb fn body

  sim_fnsem wf

  fspec_

  /\



                    (a_src: AA_src) (r_src: AR_src) (o_src: ord)
                    (PRE: P_src x_src a_src
                                exists (x_tgt: X_tgt) (a_tgt: AA_tgt) (r_tgt: AR_tgt) (o_tgt: ord)



.
  Variant fspec_weaker (fsp_src fsp_tgt: fspec): Prop :=
  | fspec_weaker_intro
      mn X_src X_tgt AA_src AA_tgt AR_src AR_tgt
      P_src P_tgt Q_src Q_tgt
      (FSPEC0: fsp_src = @mk _ mn X_src AA_src AR_src P_src Q_src)
      (FSPEC1: fsp_tgt = @mk _ mn X_tgt AA_tgt AR_tgt P_tgt Q_tgt)
      (WEAK: forall (x_src: X_src),
          exists (x_tgt: X_tgt),
            (<<PRE: forall arg varg_src o_src rarg_src
                           (PRE: P_src x_src varg_src arg o_src rarg_src),
                exists varg_tgt o_tgt rarg_tgt,
                  (<<PRE: P_tgt x_tgt varg_tgt arg o_tgt rarg_tgt>>) /\


                (a_src: AA_src) (r_src: AR_src) (o_src: ord)
                    (PRE: P_src x_src a_src
                            exists (x_tgt: X_tgt) (a_tgt: AA_tgt) (r_tgt: AR_tgt) (o_tgt: ord)


  Variant fspec_weaker (fsp_src fsp_tgt: fspec): Prop :=
  | fspec_weaker_intro
      mn X AA AR P_src P_tgt Q_src Q_tgt
      (FSPEC0: fsp_src = @mk _ mn X AA AR P_src Q_src)
      (FSPEC1: fsp_tgt = @mk _ mn X AA AR P_tgt Q_tgt)
      (WEAK: forall x aarg rarg

          (x_src: X_src) (a_src: AA_src) (r_src: AR_src) (o_src: ord)
                    (PRE: P_src x_src a_src
                                exists (x_tgt: X_tgt) (a_tgt: AA_tgt) (r_tgt: AR_tgt) (o_tgt: ord)


       .

  Variant fspec_weaker (fsp_src fsp_tgt: fspec): Prop :=
  | fspec_weaker_intro
      mn X_src X_tgt AA_src AA_tgt AR_src AR_tgt
      P_src P_tgt Q_src Q_tgt
      (FSPEC0: fsp_src = @mk _ mn X_src AA_src AR_src P_src Q_src)
      (FSPEC1: fsp_tgt = @mk _ mn X_tgt AA_tgt AR_tgt P_tgt Q_tgt)
      (WEAK: forall (x_src: X_src) (a_src: AA_src) (r_src: AR_src) (o_src: ord)
                    (PRE: P_src x_src a_src
                            exists (x_tgt: X_tgt) (a_tgt: AA_tgt) (r_tgt: AR_tgt) (o_tgt: ord)


       .

fspec

Lemma

fspec



  := fun _ => URA.of_RA RA.empty.
