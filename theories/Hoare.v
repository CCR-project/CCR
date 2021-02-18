Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Ordinal ClassicalOrdinal.
Require Import Any.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.

(* Section sealing. *)
(*   (* Local Set Primitive Projections. *) *)
(*   Record sealing X (x: X) := (* mk_sealing *) { contents_of: X; sealing_prf: contents_of = x }. *)
(* End sealing. *)
(* Ltac hide_with NAME term := *)
(*   eassert(NAME: sealing term) by (econs; eauto); *)
(*   rewrite <- sealing_prf with (s:=NAME) in * *)
(* . *)
(* Ltac hide term := *)
(*   let NAME := fresh "_SEAL" in *)
(*   hide_with NAME term *)
(* . *)
(* Ltac unhide_term term := rewrite sealing_prf with (x:=term) in *; *)
(*                     match goal with *)
(*                     | [ H: sealing term |- _ ] => clear H *)
(*                     end. *)
(* Ltac unhide_name NAME := rewrite sealing_prf with (s:=NAME) in *; clear NAME. *)
(* Ltac unhide x := *)
(*   match (type of x) with *)
(*   | sealing _ => unhide_name x *)
(*   | _ => unhide_term x *)
(*   end. *)
(* Notation "☃ y" := (@contents_of _ y _) (at level 60, only printing). (** ☁☞ **) *)
(* Goal forall x, 5 + 5 = x. i. hide 5. cbn. hide_with MYNAME x. unhide x. unhide _SEAL. cbn. Abort. *)


Module Type SEAL.
  Parameter unit: Type.
  Parameter tt: unit.
  Parameter sealing: unit -> forall X: Type, X -> X.
  Parameter sealing_eq: forall key X (x: X), sealing key x = x.
End SEAL.
Module Seal: SEAL.
  Definition unit := unit.
  Definition tt := tt.
  Definition sealing (_: unit) X (x: X) := x.
  Lemma sealing_eq key X (x: X): sealing key x = x.
  Proof. refl. Qed.
End Seal.

Ltac seal_with key x :=
  replace x with (Seal.sealing key x); [|eapply Seal.sealing_eq].
Ltac seal x :=
  let key := fresh "key" in
  assert (key:= Seal.tt);
  seal_with key x.
Ltac unseal x :=
  match (type of x) with
  | Seal.unit => repeat rewrite (@Seal.sealing_eq x) in *; try clear x
  | _ => repeat rewrite (@Seal.sealing_eq _ _ x) in *;
         repeat match goal with
                | [ H: Seal.unit |- _ ] => try clear H
                end
  end
.
Notation "☃ y" := (Seal.sealing _ y) (at level 60, only printing).
Goal forall x, 5 + 5 = x. i. seal 5. seal x. unseal key0. unseal 5. cbn. Abort.





Section PSEUDOTYPING.

(*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)) ***)
Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)

Section PROOF.
  (* Context {myRA} `{@GRA.inG myRA Σ}. *)
  Context {Σ: GRA.t}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.
  Variable mn: mname.
  Context `{X: Type}.


  Definition HoareFun
             (P: X -> Any_src -> Any_tgt -> Σ -> Prop)
             (Q: X -> Any_src -> Any_tgt -> Σ -> Prop)
             (body: Any_src -> itree Es Any_src): Any_tgt -> itree Es Any_tgt := fun varg_tgt =>
    varg_src <- trigger (Take Any_src);;
    x <- trigger (Take X);;
    rarg <- trigger (Take Σ);; forge rarg;; (*** virtual resource passing ***)
    (checkWf mn);;
    assume(P x varg_src varg_tgt rarg);; (*** precondition ***)


    vret_src <- body varg_src;; (*** "rudiment": we don't remove extcalls because of termination-sensitivity ***)

    vret_tgt <- trigger (Choose Any_tgt);;
    '(mret, fret) <- trigger (Choose _);; put mn mret fret;; (*** updating resources in an abstract way ***)
    rret <- trigger (Choose Σ);; guarantee(Q x vret_src vret_tgt rret);; (*** postcondition ***)
    (discard rret);; (*** virtual resource passing ***)

    Ret vret_tgt (*** return ***)
  .

  Definition HoareCall
             (P: X -> Any_src -> Any_tgt -> Σ -> Prop)
             (Q: X -> Any_src -> Any_tgt -> Σ -> Prop):
    gname -> Any_src -> itree Es Any_src :=
    fun fn varg_src =>
      '(marg, farg) <- trigger (Choose _);; put mn marg farg;; (*** updating resources in an abstract way ***)
      rarg <- trigger (Choose Σ);; discard rarg;; (*** virtual resource passing ***)
      x <- trigger (Choose X);; varg_tgt <- trigger (Choose Any_tgt);;
      guarantee(P x varg_src varg_tgt rarg);; (*** precondition ***)

      vret_tgt <- trigger (Call fn varg_tgt);; (*** call ***)
      checkWf mn;;

      rret <- trigger (Take Σ);; forge rret;; (*** virtual resource passing ***)
      vret_src <- trigger (Take Any_src);;
      assume(Q x vret_src vret_tgt rret);; (*** postcondition ***)

      Ret vret_src (*** return to body ***)
  .

End PROOF.















(*** TODO: Move to Coqlib. TODO: Somehow use case_ ??? ***)
(* Definition map_fst A0 A1 B (f: A0 -> A1): (A0 * B) -> (A1 * B) := fun '(a, b) => (f a, b). *)
(* Definition map_snd A B0 B1 (f: B0 -> B1): (A * B0) -> (A * B1) := fun '(a, b) => (a, f b). *)

Section CANCEL.

  Context `{Σ: GRA.t}.

  Variant hCallE: Type -> Type :=
  | hCall
      (* (mn: mname) *)
      (* (P: list val -> Σ -> Prop) (Q: list val -> Σ -> val -> Σ -> Prop) *)
      (fn: gname) (varg_src: Any_src): hCallE Any_src
  .

  (*** spec table ***)
  Record fspec: Type := mk {
    mn: mname;
    X: Type; (*** a meta-variable ***)
    precond: X -> Any_src -> Any_tgt -> Σ -> Prop; (*** meta-variable -> new logical arg -> current logical arg -> resource arg -> Prop ***)
    postcond: X -> Any_src -> Any_tgt -> Σ -> Prop; (*** meta-variable -> new logical ret -> current logical ret -> resource ret -> Prop ***)
    measure: X -> option nat;
  }
  .



  Section INTERP.
  (* Variable stb: gname -> option fspec. *)
  (*** TODO: I wanted to use above definiton, but doing so makes defining ms_src hard ***)
  (*** We can fix this by making ModSem.fnsems to a function, but doing so will change the type of
       ModSem.add to predicate (t -> t -> t -> Prop), not function.
       - Maybe not. I thought one needed to check uniqueness of gname at the "add",
         but that might not be the case.
         We may define fnsems: string -> option (list val -> itree Es val).
         When adding two ms, it is pointwise addition, and addition of (option A) will yield None when both are Some.
 ***)
  (*** TODO: try above idea; if it fails, document it; and refactor below with alist ***)
  Variable stb: list (gname * fspec).

  (****************** TODO: REMOVE ALL MATCH AND REPLACE IT WITH UNWRAPU  *****************)
  (****************** TODO: REMOVE ALL MATCH AND REPLACE IT WITH UNWRAPU  *****************)
  (****************** TODO: REMOVE ALL MATCH AND REPLACE IT WITH UNWRAPU  *****************)
  Definition handle_hCallE_src: hCallE ~> itree Es :=
    fun _ '(hCall fn varg_src) => trigger (Call fn varg_src)
  .

  Definition interp_hCallE_src `{E -< Es}: itree (hCallE +' E) ~> itree Es :=
    interp (case_ (bif:=sum1) (handle_hCallE_src)
                  ((fun T X => trigger X): E ~> itree Es))
  .

  Definition body_to_src (body: Any_src -> itree (hCallE +' pE +' eventE) Any_src): Any_src -> itree Es Any_src :=
    fun varg_src => interp_hCallE_src (body varg_src)
  .

  Definition fun_to_src (body: Any_src -> itree (hCallE +' pE +' eventE) Any_src): (Any_src -> itree Es Any_src) :=
    body_to_src body
  .





  Definition handle_hCallE_tgt (mn: mname): hCallE ~> itree Es :=
    fun _ '(hCall fn varg_src) =>
      match List.find (fun '(_fn, _) => dec fn _fn) stb with
      | Some (_, f) =>
        (HoareCall (mn) (f.(precond)) (f.(postcond)) fn varg_src)
      | None => triggerNB
      end
  .

  Definition interp_hCallE_tgt `{E -< Es} (mn: mname): itree (hCallE +' E) ~> itree Es :=
    interp (case_ (bif:=sum1) (handle_hCallE_tgt mn)
                  ((fun T X => trigger X): E ~> itree Es))
  .

  Definition body_to_tgt (mn: mname)
             (body: Any_src -> itree (hCallE +' pE +' eventE) Any_src): Any_src -> itree Es Any_src :=
    fun varg_tgt => interp_hCallE_tgt mn (body varg_tgt)
  .

  Definition fun_to_tgt (fn: gname) (body: Any_src -> itree (hCallE +' pE +' eventE) Any_src): (Any_tgt -> itree Es Any_tgt) :=
    match List.find (fun '(_fn, _) => dec fn _fn) stb with
    | Some (_, fs) => HoareFun fs.(mn) (fs.(precond)) (fs.(postcond)) (body_to_tgt fs.(mn) body)
    | _ => fun _ => triggerNB
    end.

(*** NOTE:
body can execute eventE events.
Notably, this implies it can also execute UB.
With this flexibility, the client code can naturally be included in our "type-checking" framework.
Also, note that body cannot execute "rE" on its own. This is intended.

NOTE: we can allow normal "callE" in the body too, but we need to ensure that it does not call "HoareFun".
If this feature is needed; we can extend it then. At the moment, I will only allow hCallE.
***)

  End INTERP.



  Variable md_tgt: Mod.t.
  Let ms_tgt: ModSem.t := (Mod.get_modsem md_tgt (Sk.load_skenv md_tgt.(Mod.sk))).

  Variable stb: list (gname * fspec).
  Variable ftb: list (gname * (Any.t -> itree (hCallE +' pE +' eventE) Any.t)).
  Hypothesis WTY: ms_tgt.(ModSem.fnsems) = List.map (fun '(fn, body) => (fn, fun_to_tgt stb fn body)) ftb.

  Definition ms_src: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_src body)) ftb;
    (* ModSem.initial_mrs := []; *)
    ModSem.initial_mrs := List.map (fun '(mn, (mr, mp)) => (mn, (ε, mp))) ms_tgt.(ModSem.initial_mrs);
    (*** Note: we don't use resources, so making everything as a unit ***)
  |}
  .

  Definition md_src: Mod.t := {|
    Mod.get_modsem := fun _ => ms_src;
    Mod.sk := Sk.unit;
    (*** It is already a whole-program, so we don't need Sk.t anymore. ***)
    (*** Note: Actually, md_tgt's sk could also have been unit, which looks a bit more uniform. ***)
  |}
  .



  Require Import SimSTS.

  Let W: Type := (r_state * p_state).
  Opaque GRA.to_URA.
  Let rsum: r_state -> Σ :=
    fun '(mrs_tgt, frs_tgt) => (URA.add (fold_left URA.add (List.map (mrs_tgt <*> fst) ms_tgt.(ModSem.initial_mrs)) ε)
                                        (fold_left URA.add frs_tgt ε)).
  Let wf: W -> W -> Prop :=
    fun '((mrs_src, frs_src), mps_src) '((mrs_tgt, frs_tgt), mps_tgt) =>
      (<<LEN: List.length frs_src = List.length frs_tgt>>) /\
      (<<NNIL: frs_src <> []>>) /\
      (<<WFTGT: URA.wf (rsum (mrs_tgt, frs_tgt))>>) /\
      (<<PHYS: mps_src = mps_tgt>>)
  .
  Local Opaque rsum.

  Hypothesis WF0: List.map fst ftb = List.map fst stb.
  Hypothesis WF1: Forall (fun '(_, sp) => In sp.(mn) (List.map fst ms_tgt.(ModSem.initial_mrs))) stb.

  Require Import SimGlobal.

  Lemma S_lt_O
        o
    :
      <<LT: Ordinal.lt Ordinal.O (Ordinal.S o)>>
  .
  Proof.
    r. econs. unfold Ordinal.O. unfold unit_rect. des_ifs. destruct o. econs. ii; ss.
    Unshelve.
    all: ss.
  Qed.

  Lemma le_trans: Transitive Ordinal.le. typeclasses eauto. Qed.
  Lemma lt_trans: Transitive Ordinal.le. typeclasses eauto. Qed.
  Hint Resolve Ordinal.lt_le_lt Ordinal.le_lt_lt Ordinal.add_lt_r Ordinal.add_le_l
       Ordinal.add_le_r Ordinal.lt_le
       Ordinal.S_lt_mon
       Ordinal.S_lt
       Ordinal.S_spec
       S_lt_O
    : ord.
  Hint Resolve le_trans lt_trans: ord_trans.
  Hint Resolve Ordinal.add_base_l Ordinal.add_base_r: ord_proj.

  Lemma from_nat_lt
        n m
        (LT: Nat.lt n m)
    :
      <<LT: Ordinal.lt (Ordinal.from_nat n) (Ordinal.from_nat m)>>
  .
  Proof.
    generalize dependent m. induction n; ii; ss.
    - destruct m; try lia. r; ss. eapply S_lt_O.
    - destruct m; ss; try lia. r. rewrite <- Ordinal.S_lt_mon. eapply IHn; try lia.
  Qed.

  Lemma from_nat_le
        n m
        (LT: Nat.le n m)
    :
      <<LT: Ordinal.le (Ordinal.from_nat n) (Ordinal.from_nat m)>>
  .
  Proof.
    generalize dependent m. induction n; ii; ss.
    - destruct m; try lia; ss.
    - destruct m; ss; try lia; ss. r. rewrite <- Ordinal.S_le_mon. eapply IHn; try lia.
  Qed.

  Lemma from_nat_eq
        n m
        (LT: Nat.eq n m)
    :
      <<LT: Ordinal.eq (Ordinal.from_nat n) (Ordinal.from_nat m)>>
  .
  Proof.
    generalize dependent m. induction n; ii; ss.
    - destruct m; try lia; ss.
    - destruct m; ss; try lia; ss. r. rewrite <- Ordinal.S_eq_mon. eapply IHn; try lia.
  Qed.

  Opaque Ordinal.from_nat.

  (* Ltac grind := repeat (f_equiv; try apply func_ext; ii; try (des_ifs; check_safe)). *)

  (* Ltac igo := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r; try rewrite bind_tau; *)
  (*                     try rewrite interp_vis; *)
  (*                     try rewrite interp_ret; *)
  (*                     try rewrite interp_tau *)
  (*                     (* try rewrite interp_trigger *) *)
  (*                    ). *)

  Ltac mred :=
    repeat (cbn;
            try rewrite ! interp_Es_bind; try rewrite ! interp_Es_ret; try rewrite ! interp_Es_tau;
            try rewrite ! interp_Es_rE;
            try rewrite ! interp_Es_pE;
            try rewrite ! interp_Es_eventE; try rewrite ! interp_Es_callE;
            try rewrite ! interp_Es_triggerNB; try rewrite ! interp_Es_triggerUB; (*** igo ***) ired).
  (*** step and some post-processing ***)
  Ltac _step :=
    match goal with
    (*** terminal cases ***)
    | [ |- gpaco5 _ _ _ _ _ _ _ (triggerUB >>= _) _ ] =>
      unfold triggerUB; mred; _step; ss; fail
    | [ |- gpaco5 _ _ _ _ _ _ _ (triggerNB >>= _) _ ] =>
      exfalso
    | [ |- gpaco5 _ _ _ _ _ _ _ _ (triggerUB >>= _) ] =>
      exfalso
    | [ |- gpaco5 _ _ _ _ _ _ _ _ (triggerNB >>= _) ] =>
      unfold triggerNB; mred; _step; ss; fail

    (*** assume/guarantee ***)
    | [ |- gpaco5 _ _ _ _ _ _ _ (assume ?P ;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco5 _ _ _ _ _ _ _ (guarantee ?P ;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar
    | [ |- gpaco5 _ _ _ _ _ _ _ _ (assume ?P ;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco5 _ _ _ _ _ _ _ _ (guarantee ?P ;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar

    (*** default cases ***)
    | _ =>
      (gstep; econs; eauto; try (by eapply from_nat_lt; ss);
       (*** some post-processing ***)
       i;
       try match goal with
           | [ |- (eq ==> _)%signature _ _ ] =>
             let v_src := fresh "v_src" in
             let v_tgt := fresh "v_tgt" in
             intros v_src v_tgt ?; subst v_tgt
           end)
    end
  .
  Ltac steps := repeat (mred; try _step; des_ifs_safe).
  Ltac seal_left :=
    match goal with
    | [ |- gpaco5 _ _ _ _ _ _ _ ?i_src ?i_tgt ] => seal i_src
    end.
  Ltac seal_right :=
    match goal with
    | [ |- gpaco5 _ _ _ _ _ _ _ ?i_src ?i_tgt ] => seal i_tgt
    end.
  Ltac unseal_left :=
    match goal with 
    | [ |- gpaco5 _ _ _ _ _ _ _ (@Seal.sealing _ _ ?i_src) ?i_tgt ] => unseal i_src
    end.
  Ltac unseal_right :=
    match goal with 
    | [ |- gpaco5 _ _ _ _ _ _ _ ?i_src (@Seal.sealing _ _ ?i_tgt) ] => unseal i_tgt
    end.
  Ltac force_l := seal_right; _step; unseal_right.
  Ltac force_r := seal_left; _step; unseal_left.
  (* Ltac mstep := gstep; econs; eauto; [eapply from_nat_lt; ss|]. *)

  Let adequacy_type_aux:
    forall (R: Type) (RR: R -> R -> Prop) (TY: R = (r_state * p_state * Any_src)%type)
           (REL: RR ~= (fun '((rs_src, v_src)) '((rs_tgt, v_tgt)) => wf rs_src rs_tgt /\ (v_src: Any_src) = v_tgt))
           st_src0 st_tgt0 (SIM: wf st_src0 st_tgt0) (i0: itree (hCallE +' pE +' eventE) Any_src)
           i_src i_tgt mn
           (SRC: i_src ~= (interp_Es (ModSem.prog ms_src) (interp_hCallE_src (E:=pE +' eventE) i0) st_src0))
           (TGT: i_tgt ~= (interp_Es (ModSem.prog ms_tgt) (interp_hCallE_tgt (E:=pE +' eventE) stb mn i0) st_tgt0))
    ,
    (* sim (Mod.interp md_src) (Mod.interp md_tgt) lt 100%nat *)
    (*     (x <- (interp_Es p_src (interp_hCallE_src (trigger ce)) st_src0);; Ret (snd x)) *)
    (*     (x <- (interp_Es p_tgt (interp_hCallE_tgt stb (trigger ce)) st_tgt0);; Ret (snd x)) *)
    simg RR (Ordinal.from_nat 100%nat) i_src i_tgt
  .
  Proof.
(*     i. ginit. *)
(*     { eapply cpn5_wcompat; eauto with paco. } *)
(*     (* remember (` x : ModSem.r_state * R <- interp_Es p_src (interp_hCallE_src (trigger ce)) st_src0;; Ret (snd x)) as tmp. *) *)
(*     revert_until R. revert R. *)
(*     unfold Relation_Definitions.relation. *)
(*     gcofix CIH. i; subst. *)
(*     (* intros ? ?. *) *)
(*     (* pcofix CIH. i. *) *)
(*     unfold interp_hCallE_src. *)
(*     unfold interp_hCallE_tgt. *)
(*     ides i0; try rewrite ! unfold_interp; cbn; mred. *)
(*     { steps. } *)
(*     { steps. gbase. eapply CIH; [..|M]; Mskip et. *)
(*       { refl. } *)
(*       { instantiate (1:=mn0). fold (interp_hCallE_tgt stb mn0). ss. } *)
(*     } *)
(*     destruct e; cycle 1. *)
(*     { *)
(*       Opaque interp_Es. *)
(*       destruct s; ss. *)
(*       { *)
(*         destruct st_src0 as [rst_src0 pst_src0], st_tgt0 as [rst_tgt0 pst_tgt0]; ss. des_ifs. des; clarify. *)
(*         destruct p; ss. *)
(*         - steps. gbase. eapply CIH; [refl|ss|..]; cycle 1. *)
(*           { unfold interp_hCallE_src. refl. } *)
(*           { unfold interp_hCallE_tgt. refl. } *)
(*           ss. *)
(*         - steps. gbase. eapply CIH; [refl|ss|..]; cycle 1. *)
(*           { unfold interp_hCallE_src. refl. } *)
(*           { unfold interp_hCallE_tgt. refl. } *)
(*           ss. *)
(*       } *)
(*       { dependent destruction e. *)
(*         - steps. esplits; eauto. steps. *)
(*           gbase. eapply CIH; [..|M]; Mskip et. *)
(*           { refl. } *)
(*           { instantiate (2:=mn0). fold (interp_hCallE_tgt stb mn0). ss. } *)
(*         - steps. esplits; eauto. steps. *)
(*           gbase. eapply CIH; [..|M]; Mskip et. *)
(*           { refl. } *)
(*           { instantiate (1:=mn0). fold (interp_hCallE_tgt stb mn0). ss. } *)
(*         - steps. *)
(*           gbase. eapply CIH; [..|M]; Mskip et. *)
(*           { refl. } *)
(*           { instantiate (1:=mn0). fold (interp_hCallE_tgt stb mn0). ss. } *)
(*       } *)
(*     } *)
(*     dependent destruction h. *)
(*     Local Opaque GRA.to_URA. *)
(*     ss. *)
(*     seal_left. *)
(*     steps. *)
(*     des_ifs; cycle 1. *)
(*     { steps. } *)
(*     rename Heq into FINDFT. *)
(*     (* unfold ModSem.prog at 2. steps. *) *)
(*     unfold HoareCall. *)
(*     steps. unfold put, guarantee. steps. *)
(*     destruct st_tgt0 as [rst_tgt0 pst_tgt0]. destruct st_src0 as [rst_src0 pst_src0]. *)
(*     Opaque interp_Es. (*** TODO: move to ModSem ***) *)
(*     steps. unfold handle_rE. des_ifs. *)
(*     { rr in SIM. des_ifs. des; ss. destruct l; ss. } *)
(*     steps. unfold guarantee. (*** TODO: remove: unfold guarantee ***) *)
(*     (* do 2 (mred; try _step; des_ifs_safe). *) *)
(*     (* unseal_left. *) *)
(*     (* seal_right. _step. exists (x2↑). mred. unseal_right. *) *)
(*     (* _step. instantiate (1:=Ordinal.from_nat 300). *) *)
(*     unseal_left. *)
(*     steps. *)
(*     unfold unwrapU at 1. des_ifs; cycle 1. *)
(*     { steps. } *)
(*     rename Heq into FINDFS. *)
(*     unfold discard. *)
(*     steps. *)
(*     unfold guarantee. *)
(*     steps. *)
(*     unfold unwrapU. des_ifs; cycle 1. *)
(*     { steps. *)
(*       rewrite WTY in *. ss. clear - FINDFS Heq. *)
(*       rewrite find_map in *. uo. des_ifs. *)
(*       Fail apply_all_once find_some. (*** TODO: FIXME ****) *)
(*       apply find_some in Heq1. des. *)
(*       eapply find_none in Heq0; eauto. *)
(*       unfold compose in *. des_ifs. ss. clarify. *)
(*     } *)
(*     rename Heq into FINDFT0. *)
(*     unfold handle_rE. des_ifs. *)
(*     { steps. rr in SIM. des; ss. } *)
(*     steps. *)
(*     rename i into i_src. *)
(*     rename i0 into i_tgt. *)
(*     guclo bindC_spec. *)
(*     instantiate (1:=400). *)
(*     replace (Ordinal.from_nat 400) with *)
(*         (Ordinal.add (Ordinal.from_nat 200) (Ordinal.from_nat 200)); cycle 1. *)
(*     { admit "ez". } *)
(*     rename f into fs. *)
(*     econs. *)
(*     - instantiate (1:= fun '((((mrs_src, frs_src), mps_src), vret_src): (r_state * p_state * Any_src)) *)
(*                            '((((mrs_tgt, frs_tgt), mps_tgt), vret_tgt): (r_state * p_state * Any_tgt)) => *)
(*                          exists (rret: Σ), *)
(*                            (<<ST: (List.length frs_src) = (List.length frs_tgt) /\ *)
(*                                   frs_src <> [] /\ *)
(*                                   URA.wf (rsum (mrs_tgt, rret :: frs_tgt))>>) /\ *)
(*                            (* (<<VAL: vret_src = vret_tgt>>) /\ *) *)
(*                            (<<POST: fs.(postcond) x2 vret_src vret_tgt rret>>) /\ *)
(*                            (<<PHYS: mps_src = mps_tgt>>) *)
(*                   ). *)
(*       apply find_some in FINDFT0. des. *)
(*       apply find_some in FINDFS. des. ss. des_sumbool. clarify. *)
(*       rewrite WTY in *. fold Any_src in FINDFS. fold Any_tgt in FINDFT0. rewrite in_map_iff in *. des. des_ifs. *)
(*       fold Any_tgt in x3. *)
(*       unfold fun_to_src, fun_to_tgt. des_ifs. unfold HoareFun. *)
(*       rename x3 into PRECOND. rename x0 into rarg. *)
(*       steps. exists varg_src. *)
(*       steps. esplits; et. steps. exists rarg. *)
(*       steps. unfold forge, checkWf. steps. unfold assume, guarantee. *)
(* Infix "⋅" := URA.add (at level 50, left associativity). *)
(* Notation "(⋅)" := URA.add (only parsing). *)
(*       steps. unshelve esplits; eauto. *)
(*       { clear - WFTGT x. rewrite URA.unit_idl. rewrite URA.add_assoc in x. *)
(*         r in x. specialize (x URA.unit). rewrite ! URA.unit_id in x. *)
(*         unfold update. des_ifs. *)
(*         - eapply URA.wf_mon. eapply x. admit "ez - WFTGT". *)
(*         - admit "ez - c1 contains both (c1 mn0) and (c1 (mn fs)).". *)
(*       } *)
(*       steps. esplits; eauto. steps. *)
(*       (* esplits; eauto. *) *)
(*       (* { clear - WFTGT x0. rewrite URA.unit_idl. rewrite URA.add_assoc in x0. *) *)
(*       (*   r in x0. specialize (x0 URA.unit). rewrite ! URA.unit_id in x0. *) *)
(*       (*   unfold update. des_ifs. *) *)
(*       (*   - eapply URA.wf_mon. eapply x0. admit "ez - WFTGT". *) *)
(*       (*   - admit "ez - c1 contains both (c1 mn0) and (c1 (mn fs)).". *) *)
(*       (* } *) *)
(*       (* steps. unfold assume. steps. *) *)
(*       (* esplits; eauto. steps. *) *)
(*       unfold body_to_src, body_to_tgt. *)
(*       guclo bindC_spec. *)
(*       replace (Ordinal.from_nat 172) with (Ordinal.add (Ordinal.from_nat 42) (Ordinal.from_nat 130)); cycle 1. *)
(*       { admit "ez - ordinal nat add". } *)
(*       rewrite idK_spec at 1. *)
(*       assert(i0 = i) by admit "ez - uniqueness of idx. Add this as an hypothesis". subst. *)
(*       econs. *)
(*       + guclo ordC_spec. econs; eauto. { instantiate (1:=Ordinal.from_nat 100). eapply from_nat_le; ss. lia. } *)
(*         gbase. *)
(*         eapply CIH; et. *)
(*         { refl. } *)
(*         ss. esplits; ss; et. *)
(*         clear - WFTGT x. *)
(*         rewrite URA.unit_idl. *)
(*         admit "ez -- updatable". *)
(*       + bar. ii. des_ifs. des; subst. rename a into a_src. *)
(*         unfold idK. *)
(*         steps. unfold handle_rE. *)
(*         r in SIM. des_ifs; ss. des; ss. destruct l; ss. des; ss. *)
(*         steps. unfold put. unfold guarantee. steps. *)
(*         unfold discard. unfold guarantee. steps. *)
(*         esplits; et. *)
(*         clear - WFTGT0 x3. *)
(*         admit "ez -- updtaable". *)
(*     - ii. ss. des_ifs. des. (* rr in SIM0. des; ss. unfold RelationPairs.RelCompFun in *. ss. *) *)
(*       (* r in SIM0. des_ifs. des; ss. *) *)
(*       steps. clear_tac. instantiate (1:=125). *)
(*       unfold checkWf, assume; steps. *)
(*       des_ifs; ss. *)
(*       { steps. } *)
(*       steps. *)
(*       unshelve esplits; eauto. *)
(*       { clear - ST1. admit "ez". } *)
(*       steps. esplits; eauto. *)
(*       unfold forge; steps. exists t. *)
(*       steps. unshelve esplits; eauto. steps. *)
(*       fold interp_hCallE_src. fold (interp_hCallE_tgt stb mn0). *)
(*       gbase. eapply CIH; [refl|ss|..]; cycle 1. *)
(*       { refl. } *)
(*       { unfold interp_hCallE_tgt. refl. } *)
(*       rr. esplits; et. { destruct l3; ss. } clear - ST1. admit "ez". *)
(*   Unshelve. *)
(*     all: ss. *)
(*     all: try (by apply Ordinal.O). *)
    admit "tmp".
  Qed.

  Hypothesis MAIN: List.find (fun '(_fn, _) => dec "main" _fn) stb = Some ("main",
    (* (@mk "Main" unit (fun _ varg_high _ _ => varg_high = tt↑) (fun _ vret_high _ _ => vret_high = tt↑) (fun _ => None))). *)
    (@mk "Main" unit (fun _ varg_high varg_low _ => varg_high = varg_low) (fun _ vret_high vret_low _ => vret_high = vret_low) (fun _ => None))).
  Hypothesis WFR: URA.wf (rsum (ModSem.initial_r_state ms_tgt)).

  Opaque interp_Es.
  Theorem adequacy_type: Beh.of_program (Mod.interp md_tgt) <1= Beh.of_program (Mod.interp md_src).
  Proof.
    eapply adequacy_global.
    exists (Ordinal.from_nat 100%nat). ss.
    ginit.
    { eapply cpn5_wcompat; eauto with paco. }
    unfold ModSem.initial_itr. Local Opaque ModSem.prog. ss.
    unfold ITree.map.
    unfold assume.
    steps.
    esplits; et. { admit "ez - wf". }
    set (st_src0 := ((ModSem.initial_r_state ms_src), (ModSem.initial_p_state ms_src))).
    replace (Mod.enclose md_tgt) with ms_tgt by ss.
    set (st_tgt0 := ((ModSem.initial_r_state ms_tgt), (ModSem.initial_p_state ms_tgt))).
    (* Local Opaque URA.add. *)
    assert(SIM: wf st_src0 st_tgt0).
    { r. ss. esplits; ss; et. unfold ms_src. unfold ModSem.initial_p_state. ss.
      apply func_ext. clear - Σ. i. rewrite find_map; ss. unfold compose. uo.
      replace (fun x0 : string * (Σ * Any.t) => (dec x (fst (let '(mn0, (_, mp)) := x0 in (mn0, (ε, mp))))): bool) with
          (fun mnr : string * (Σ * Any.t) => (dec x (fst mnr)): bool); cycle 1.
      { apply func_ext. i. des_ifs. }
      des_ifs; eq_closure_tac.
    }
    unfold mrec.
    (* { *)
    (*   unfold ModSem.prog at 4. *)
    (*   unfold ModSem.prog at 2. *)
    (*   unfold unwrapU at 1. des_ifs; cycle 1. { steps. } steps. *)
    (*   rename Heq into MAINSRC. rename i into i_src. *)
    (*   assert(T: exists i_ftb i_tgt, *)
    (*             (<<MAINTGT:find (fun fnsem => dec "main" (fst fnsem)) (ModSem.fnsems ms_tgt) = *)
    (*                        Some ("main", i_tgt)>>) *)
    (*             /\ (<<FTB: In ("main", i_ftb) ftb>>) *)
    (*             /\ (<<SIM: i_tgt = fun_to_tgt stb "main" i_ftb>>) *)
    (*             /\ (<<SIM: i_src = fun_to_src i_ftb>>) *)
    (*         ). *)
    (*   { apply find_some in MAINSRC. des; ss. des_sumbool. clarify. *)
    (*     apply in_map_iff in MAINSRC. des. des_ifs. *)
    (*     destruct (find (fun fnsem => dec "main" (fst fnsem)) (ModSem.fnsems ms_tgt)) eqn:T; *)
    (*       rewrite WTY in *; ss; cycle 1. *)
    (*     - eapply find_none in T; ss; et. *)
    (*       { des_sumbool. instantiate (1:= (_, _)) in T. ss. } *)
    (*       rewrite in_map_iff. eexists (_, _). esplits; et. *)
    (*     - apply find_some in T. des; ss. des_sumbool. destruct p; ss. clarify. *)
    (*       rewrite in_map_iff in T. des; ss. des_ifs. *)
    (*       esplits; et. assert(i = i1) by admit "ez - add nodup". clarify. *)
    (*   } *)
    (*   des. clarify. *)
    (*   unfold unwrapU. des_ifs; cycle 1. steps. *)
    (*   unfold fun_to_tgt. des_ifs. ss. unfold fun_to_src. unfold HoareFun. *)
    (*   steps. esplits; et. steps. esplits; et. steps. *)
    (* } *)
    assert(TRANSL: simg eq (Ordinal.from_nat 100)
(x0 <- interp_Es (ModSem.prog ms_src)
                 ((ModSem.prog ms_src) _ (Call "main" tt↑)) st_src0;; Ret (snd x0))
(x0 <- interp_Es (ModSem.prog ms_src)
                 (interp_hCallE_src (E:=pE +' eventE) (trigger (hCall "main" tt↑))) st_src0;; Ret (snd x0))).
    { clear SIM. ginit. { eapply cpn5_wcompat; eauto with paco. }
      unfold interp_hCallE_src. rewrite unfold_interp. ss. cbn. steps.
      replace (Ordinal.from_nat 99) with (Ordinal.add (Ordinal.from_nat 50) (Ordinal.from_nat 49))
        by admit "ez".
      guclo bindC_spec.
      eapply bindR_intro with (RR:=eq).
      - eapply simg_gpaco_refl. typeclasses eauto.
      - ii. des_ifs. ss. steps.
    }
    assert(TRANSR: simg eq (Ordinal.from_nat 100)
(x0 <- interp_Es (ModSem.prog ms_tgt)
                 (interp_hCallE_tgt (E:=pE +' eventE) stb "Main" (trigger (hCall "main" tt↑))) st_tgt0;; Ret (snd x0))
(x0 <- interp_Es (ModSem.prog ms_tgt)
                 ((ModSem.prog ms_tgt) _ (Call "main" tt↑)) st_tgt0;; Ret (snd x0))).
    { clear SIM. ginit. { eapply cpn5_wcompat; eauto with paco. }
      unfold interp_hCallE_tgt. rewrite unfold_interp. steps.
      unfold HoareCall.
      destruct (find (fun mnr => dec "Main" (fst mnr)) (ModSem.initial_mrs ms_tgt)) eqn:MAINR; cycle 1.
      { exfalso. clear - WF1 Heq MAINR. admit "ez - use WF1". }
      destruct p; ss.
      assert(s = "Main") by admit "ez". clarify.
      (* rewrite Any.upcast_downcast. *)
      steps. eexists ((fst (fst st_tgt0)) "Main", ε). steps.
      unfold put, guarantee. steps. unfold st_tgt0. steps.
      ss.
      unshelve esplits; eauto.
      { refl. }
      steps. esplits; et. steps. unfold discard, guarantee. steps. esplits; et. steps. unshelve esplits; et.
      { instantiate (1:=ε). rewrite URA.unit_id. ss. }
      steps. unfold guarantee. steps. esplits; et. steps. exists (tt↑).
      replace (update
                 (fun mn0 : string =>
                    match find (fun mnr => dec mn0 (fst mnr)) (ModSem.initial_mrs ms_tgt) with
                    | Some r => fst (snd r)
                    | None => ε
                    end) "Main" (fst p), [ε], ModSem.initial_p_state ms_tgt) with st_tgt0; cycle 1.
      { unfold st_tgt0.
        unfold ModSem.initial_r_state. f_equal. f_equal. apply func_ext. i. unfold update. des_ifs; ss; clarify. }
      steps. esplits; et. steps.
      replace (Ordinal.from_nat 55) with (Ordinal.add (Ordinal.from_nat 25) (Ordinal.from_nat 30)) by admit "ez".
      guclo bindC_spec.
      eapply bindR_intro with (RR:=eq).
      - fold st_tgt0. eapply simg_gpaco_refl. typeclasses eauto.
      - ii. des_ifs. ss. steps.
        unfold checkWf, assume. steps. destruct p0. steps.
        unfold ModSem.handle_rE. des_ifs.
        { admit "we should use stronger RR, not eq;
we should know that stackframe is not popped (unary property)". }
        steps. unfold forge; steps.
    }



    replace (x0 <- interp_Es (ModSem.prog ms_src) ((ModSem.prog ms_src) _ (Call "main" tt↑)) st_src0;;
             Ret (snd x0)) with
        (x0 <- interp_Es (ModSem.prog ms_src) (interp_hCallE_src (E:=pE +' eventE) (trigger (hCall "main" tt↑))) st_src0;;
         Ret (snd x0)); cycle 1.
    { admit "hard -- by transitivity". }
    replace (x0 <- interp_Es (ModSem.prog ms_tgt) ((ModSem.prog ms_tgt) _ (Call "main" tt↑)) st_tgt0;;
             Ret (snd x0)) with
        (x0 <- interp_Es (ModSem.prog ms_tgt) (interp_hCallE_tgt (E:=pE +' eventE) stb "Main" (trigger (hCall "main" tt↑)))
                         st_tgt0;; Ret (snd x0)); cycle 1.
    { admit "hard -- by transitivity". }
    guclo bindC_spec.
    eapply bindR_intro.
    - gfinal. right. fold simg. eapply adequacy_type_aux; ss. subst st_src0 st_tgt0. ss.
    - ii. ss. des_ifs. des; ss. clarify. steps.
  Unshelve.
    all: ss.
    all: try (by apply Ordinal.O).
  Qed.

End CANCEL.

End PSEUDOTYPING.
