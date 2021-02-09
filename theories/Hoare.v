Require Import Coqlib.
Require Import ITreelib.
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



Section PROOF.
  (* Context {myRA} `{@GRA.inG myRA Σ}. *)
  Context {Σ: GRA.t}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.
  Variable mn: mname.
  Context `{X: Type}.

  Definition HoareFun
             (P: X -> Any.t -> Σ -> Prop)
             (Q: X -> Any.t -> Σ -> Prop)
             (body: Any.t -> itree Es Any.t): Any.t -> itree Es Any.t := fun varg =>
    x <- trigger (Take X);;
    rarg <- trigger (Take Σ);; trigger (Forge rarg);; (*** virtual resource passing ***)
    trigger (CheckWf mn);;
    assume(P x varg rarg);; (*** precondition ***)


    vret <- body varg;; (*** "rudiment": we don't remove extcalls because of termination-sensitivity ***)

    '(mret, fret) <- trigger (Choose _);; trigger (Put mn mret fret);; (*** updating resources in an abstract way ***)
    rret <- trigger (Choose Σ);; guarantee(Q x vret rret);; (*** postcondition ***)
    trigger (Discard rret);; (*** virtual resource passing ***)

    Ret vret (*** return ***)
  .

  Definition HoareCall
             (P: X -> Any.t -> Σ -> Prop)
             (Q: X -> Any.t -> Σ -> Prop):
    fname -> Any.t -> itree Es Any.t :=
    fun fn varg =>
      '(marg, farg) <- trigger (Choose _);; trigger (Put mn marg farg);; (*** updating resources in an abstract way ***)
      rarg <- trigger (Choose Σ);; trigger (Discard rarg);; (*** virtual resource passing ***)
      x <- trigger (Choose X);;
      guarantee(P x varg rarg);; (*** precondition ***)

      vret <- trigger (Call fn varg);; (*** call ***)
      trigger (CheckWf mn);;

      rret <- trigger (Take Σ);; trigger (Forge rret);; (*** virtual resource passing ***)
      assume(Q x vret rret);; (*** postcondition ***)

      Ret vret (*** return to body ***)
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
      (fn: fname) (varg: Any.t): hCallE Any.t
  .

  (*** spec table ***)
  Record fspec: Type := mk {
    mn: mname;
    X: Type; (*** a meta-variable ***)
    precond: X -> Any.t -> Σ -> Prop;
    postcond: X -> Any.t -> Σ -> Prop;
  }
  .



  Section INTERP.
  (* Variable stb: fname -> option fspec. *)
  (*** TODO: I wanted to use above definiton, but doing so makes defining ms_src hard ***)
  (*** We can fix this by making ModSem.fnsems to a function, but doing so will change the type of
       ModSem.add to predicate (t -> t -> t -> Prop), not function.
       - Maybe not. I thought one needed to check uniqueness of fname at the "add",
         but that might not be the case.
         We may define fnsems: string -> option (list val -> itree Es val).
         When adding two ms, it is pointwise addition, and addition of (option A) will yield None when both are Some.
 ***)
  (*** TODO: try above idea; if it fails, document it; and refactor below with alist ***)
  Variable stb: list (fname * fspec).

  Definition handle_hCallE_tgt (mn: mname): hCallE ~> itree Es :=
    fun _ '(hCall fn varg) =>
      match List.find (fun '(_fn, _) => dec fn _fn) stb with
      | Some (_, f) =>
        (HoareCall (mn) (f.(precond)) (f.(postcond)) fn varg)
      | None => triggerNB
      end
  .

  Definition interp_hCallE_tgt (mn: mname): itree (hCallE +' eventE) ~> itree Es :=
    interp (case_ (bif:=sum1) (handle_hCallE_tgt mn)
                  ((fun T X => trigger X): eventE ~> itree Es))
  .

  Definition body_to_tgt (mn: mname)
             (body: Any.t -> itree (hCallE +' eventE) Any.t): Any.t -> itree Es Any.t :=
    fun varg => interp_hCallE_tgt mn (body varg)
  .



  Definition handle_hCallE_src: hCallE ~> itree Es :=
    fun _ '(hCall fn varg) => trigger (Call fn varg)
  .

  Definition interp_hCallE_src: itree (hCallE +' eventE) ~> itree Es :=
    interp (case_ (bif:=sum1) handle_hCallE_src
                  ((fun T X => trigger X): eventE ~> itree Es))
  .

  Definition body_to_src (body: Any.t -> itree (hCallE +' eventE) Any.t): Any.t -> itree Es Any.t :=
    fun varg => interp_hCallE_src (body varg)
  .
  Definition fun_to_tgt (fn: fname) (body: Any.t -> itree (hCallE +' eventE) Any.t): (Any.t -> itree Es Any.t) :=
    match List.find (fun '(_fn, _) => dec fn _fn) stb with
    | Some (_, fs) => HoareFun fs.(mn) (fs.(precond)) (fs.(postcond)) (body_to_tgt fs.(mn) body)
    | _ => fun _ => triggerNB
    end.
  Definition fun_to_src (body: Any.t -> itree (hCallE +' eventE) Any.t): (Any.t -> itree Es Any.t) :=
    body_to_src body.

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

  Variable stb: list (fname * fspec).
  Variable ftb: list (fname * (Any.t -> itree (hCallE +' eventE) Any.t)).
  Hypothesis WTY: ms_tgt.(ModSem.fnsems) = List.map (fun '(fn, body) => (fn, fun_to_tgt stb fn body)) ftb.

  Definition ms_src: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_src body)) ftb;
    ModSem.initial_mrs := [];
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

  Ltac grind := repeat (f_equiv; try apply func_ext; ii; try (des_ifs; check_safe)).

  Ltac igo := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r; try rewrite bind_tau;
                      try rewrite interp_vis;
                      try rewrite interp_ret;
                      try rewrite interp_tau
                      (* try rewrite interp_trigger *)
                     ).

  Let W: Type := ((string -> Σ) * list Σ).
  Opaque GRA.to_URA.
  Let rsum: W -> Σ :=
    fun '(mrs_tgt, frs_tgt) => (URA.add (fold_left URA.add (List.map (mrs_tgt <*> fst) ms_tgt.(ModSem.initial_mrs)) ε)
                                        (fold_left URA.add frs_tgt ε)).
  Let wf: W -> W -> Prop :=
    fun '(mrs_src, frs_src) '(mrs_tgt, frs_tgt) =>
      (<<LEN: List.length frs_src = List.length frs_tgt>>) /\
      (<<NNIL: frs_src <> []>>) /\
      (<<WFTGT: URA.wf (rsum (mrs_tgt, frs_tgt))>>)
  .
  Local Opaque rsum.

  Hypothesis WF0: List.map fst ftb = List.map fst stb.
  Hypothesis MAIN: List.find (fun '(_fn, _) => dec "main" _fn) stb = Some ("main", (@mk "Main" unit top3 top3)).
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
  Opaque string_dec.

  Ltac mgo := repeat (try rewrite ! interp_Es_bind; try rewrite ! interp_Es_ret; try rewrite ! interp_Es_tau;
                      try rewrite ! interp_Es_rE; try rewrite ! interp_Es_eventE; try rewrite ! interp_Es_callE;
                      try rewrite ! interp_Es_triggerNB; try rewrite ! interp_Es_triggerUB; igo).
  Ltac mstep := gstep; econs; eauto; [eapply from_nat_lt; ss|].

  Let adequacy_type_aux:
    forall (R: Type) (RR: R -> R -> Prop) (TY: R = (ModSem.r_state * Any.t)%type)
           (REL: RR ~= (fun '(rs_src, v_src) '(rs_tgt, v_tgt) => wf rs_src rs_tgt /\ (v_src: Any.t) = v_tgt))
           st_src0 st_tgt0 (SIM: wf st_src0 st_tgt0) (i0: itree (hCallE +' eventE) Any.t)
           i_src i_tgt mn
           (SRC: i_src ~= (interp_Es (ModSem.prog ms_src) (interp_hCallE_src i0) st_src0))
           (TGT: i_tgt ~= (interp_Es (ModSem.prog ms_tgt) (interp_hCallE_tgt stb mn i0) st_tgt0))
    ,
    (* sim (Mod.interp md_src) (Mod.interp md_tgt) lt 100%nat *)
    (*     (x <- (interp_Es p_src (interp_hCallE_src (trigger ce)) st_src0);; Ret (snd x)) *)
    (*     (x <- (interp_Es p_tgt (interp_hCallE_tgt stb (trigger ce)) st_tgt0);; Ret (snd x)) *)
    simg RR (Ordinal.from_nat 100%nat) i_src i_tgt
  .
  Proof.
    i. ginit.
    { eapply cpn5_wcompat; eauto with paco. }
    (* remember (` x : ModSem.r_state * R <- interp_Es p_src (interp_hCallE_src (trigger ce)) st_src0;; Ret (snd x)) as tmp. *)
    revert_until R. revert R.
    unfold Relation_Definitions.relation.
    gcofix CIH. i; subst.
    (* intros ? ?. *)
    (* pcofix CIH. i. *)
    unfold interp_hCallE_src.
    unfold interp_hCallE_tgt.
    ides i0; try rewrite ! unfold_interp; cbn; mgo.
    { ss. gstep. econs; eauto. }
    { ss. gstep. econs; eauto. gbase. eapply CIH; [..|M]; Mskip et.
      { instantiate (1:=mn0). fold (interp_hCallE_tgt stb mn0). ss. }
    }
    destruct e; cycle 1.
    { dependent destruction e.
      - cbn. mgo. gstep. econs; eauto. i. esplits; eauto.
        mgo. gstep. econs; eauto.
        mgo. gstep. econs; eauto.
        mgo. gstep. econs; eauto.
        gbase. eapply CIH; [..|M]; Mskip et.
        { instantiate (2:=mn0). fold (interp_hCallE_tgt stb mn0). ss. }
      - cbn. mgo. gstep. econs; eauto. i. esplits; eauto.
        mgo. gstep. econs; eauto.
        mgo. gstep. econs; eauto.
        mgo. gstep. econs; eauto.
        gbase. eapply CIH; [..|M]; Mskip et.
        { instantiate (1:=mn0). fold (interp_hCallE_tgt stb mn0). ss. }
      - cbn. mgo. gstep. econs; eauto. ii; clarify.
        mgo. gstep. econs; eauto.
        mgo. gstep. econs; eauto.
        mgo. gstep. econs; eauto.
        gbase. eapply CIH; [..|M]; Mskip et.
        { instantiate (1:=mn0). fold (interp_hCallE_tgt stb mn0). ss. }
    }
    dependent destruction h.
    Local Opaque GRA.to_URA.
    ss.
    mgo. cbn. mgo.
    mstep.

    (* gstep. econs; eauto. { eapply from_nat_lt; ss. } left. *)
    (* gstep. econs; eauto. { eapply from_nat_lt; ss. } left. *)
    des_ifs; cycle 1.
    { gstep. mgo. unfold triggerNB. mgo. econs; ss; eauto. { eapply from_nat_lt; ss. } }
    rename Heq into FINDFT.
    unfold ModSem.prog at 3. mgo.
    unfold unwrapU. des_ifs; cycle 1.
    { gstep. mgo. unfold triggerUB. mgo. econs; ss; eauto. { eapply from_nat_lt; ss. } }
    mgo. des_ifs. mgo.
    unfold ModSem.handle_rE. des_ifs.
    { rr in SIM. des_ifs. des; ss. }
    mgo.
    unfold HoareCall. mgo.
    gstep. econsr; eauto. { eapply from_nat_lt; ss. } i.
    mgo. gstep. econs; eauto.
    mgo. gstep. econs; eauto. instantiate (1:=Ordinal.from_nat 300).
    mgo. des_ifs. rename Heq into FINDFS. rename i into i_src.
    mgo. unfold handle_rE. des_ifs.
    { gstep. mgo. unfold triggerNB. mgo. econs; ss; eauto. { eapply from_nat_lt; ss. } }
    mgo. unfold guarantee.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. }
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. }
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. }
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. }
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. }
    cbn.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
    mgo. unfold guarantee.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
    unfold ModSem.prog at 7. mgo. cbn.
    unfold unwrapU. des_ifs; cycle 1.
    { exfalso. rewrite WTY in *. ss. clear - FINDFS Heq.
      rewrite find_map in *. uo. des_ifs.
      Fail apply_all_once find_some. (*** TODO: FIXME ****)
      apply find_some in Heq1. des.
      eapply find_none in Heq0; eauto.
      unfold compose in *. ss. clarify. }
    rename Heq into FINDFT0.
    mgo. des_ifs. rename i into i_tgt.
    mgo. cbn.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
    mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
    guclo bindC_spec.
    replace (Ordinal.from_nat 281) with (Ordinal.add (Ordinal.from_nat 141) (Ordinal.from_nat 140)); cycle 1.
    { admit "ez - ordinal nat add". }
    rename f into fs.
    econs.
    - instantiate (1:= fun '((mrs_src, frs_src), vret_src) '((mrs_tgt, frs_tgt), vret_tgt) =>
                         exists (rret: Σ),
                           (<<ST: (List.length frs_src) = (List.length frs_tgt) /\
                                  frs_src <> [] /\
                                  URA.wf (rsum (mrs_tgt, rret :: frs_tgt))>>) /\
                           (<<VAL: vret_src = vret_tgt>>) /\
                           (<<POST: fs.(postcond) x3 vret_tgt rret>>)).
      apply find_some in FINDFT0. des.
      apply find_some in FINDFS. des. ss. des_sumbool. clarify.
      rewrite WTY in *. rewrite in_map_iff in *. des. des_ifs.
      unfold fun_to_src, fun_to_tgt. des_ifs. unfold HoareFun.
      (* unfold body_to_src. *)
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i. exists x3.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i. exists x0.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i. cbn.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i. cbn. unfold assume.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i. esplits; eauto.
Infix "⋅" := URA.add (at level 50, left associativity).
Notation "(⋅)" := URA.add (only parsing).
      { clear - WFTGT x. admit "<<WFTGT: wf (Σ c1 + Σ l1 + c4)>>
--(apply x)-->
wf (Σ c1 [mn := c2] + Σ l1 + (x0 + x1))
".
      }
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i. esplits; eauto.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
      unfold body_to_src, body_to_tgt. des_ifs.
      guclo bindC_spec.
      replace (Ordinal.from_nat 126) with (Ordinal.add (Ordinal.from_nat 18) (Ordinal.from_nat 108)); cycle 1.
      { admit "ez - ordinal nat add". }
      rewrite idK_spec at 1.
      assert(i0 = i) by admit "ez - uniqueness of idx. Add this as an hypothesis". subst.
      econs.
      + guclo ordC_spec. econs; eauto. { instantiate (1:=Ordinal.from_nat 100). eapply from_nat_le; ss. lia. }
        gbase. eapply CIH; et.
        { refl. }
        ss. esplits; ss; et.
        clear - WFTGT x.
        admit "ez -- updatable".
      + ii. des_ifs. des; subst.
        unfold idK.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        des_ifs. r in SIM. des_ifs; ss. des; ss.
        mgo. unfold ModSem.handle_rE. des_ifs; ss. { destruct l; ss. }
        unfold guarantee.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        cbn.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        unfold guarantee.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
        mgo. gstep. econs; eauto. esplits; eauto.
        clear - WFTGT0 x8 x2.
        admit "ez".
    - ii. ss. des_ifs. des. (* rr in SIM0. des; ss. unfold RelationPairs.RelCompFun in *. ss. *)
      (* r in SIM0. des_ifs. des; ss. *)
      mgo. unfold ModSem.handle_rE. des_ifs.
      (* { unfold triggerNB. mgo. gstep. eapply simg_chooseR; eauto. { eapply from_nat_lt; ss. } ss. } *)
      mgo. gstep. econs; eauto. i.
      mgo. gstep. econs; eauto. i.
      instantiate (1:= Ordinal.from_nat 113).
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
      cbn. des_ifs; ss.
      { unfold triggerNB. mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } ss. }
      unfold assume.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
      esplits; eauto.
      { clear - ST1. admit "ez". }
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } i.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } eexists rret.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. }
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. }
      cbn.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. }
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. }
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. } esplits; eauto.
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. }
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. }
      mgo. gstep. econs; eauto. { eapply from_nat_lt; ss. }
      fold interp_hCallE_src. fold (interp_hCallE_tgt stb).
      gbase. eapply CIH; [..|M]; Mskip et. all: cycle 1.
      { instantiate (2:=mn0). fold (interp_hCallE_tgt stb mn0). ss. }
      rr. esplits; et. { destruct l3; ss. } clear - ST1. admit "ez".
  Unshelve.
    all: ss.
    all: try (by apply Ordinal.O).
  Qed.

  Hypothesis WFR: URA.wf (rsum (ModSem.initial_r_state ms_tgt)).

  Theorem adequacy_type: Beh.of_program (Mod.interp md_tgt) <1= Beh.of_program (Mod.interp md_src).
  Proof.
    eapply adequacy_global.
    exists (Ordinal.from_nat 100%nat).
    ss. unfold ModSem.initial_itr. Local Opaque ModSem.prog. ss.
    unfold ITree.map.
    unfold assume.
    igo.
    pfold. eapply simg_takeL; ss.
    { instantiate (1:= (Ordinal.from_nat 99)). admit "ez". }
    i. left.
    pfold. eapply simg_takeR; ss.
    { instantiate (1:= (Ordinal.from_nat 98)). admit "ez". }
    esplits; et. { admit "ez - wf". } left.
    set (st_src0 := (ModSem.initial_r_state ms_src)).
    replace (Mod.enclose md_tgt) with ms_tgt by ss.
    set (st_tgt0 := (ModSem.initial_r_state ms_tgt)).
    (* Local Opaque URA.add. *)
    assert(SIM: wf st_src0 st_tgt0).
    { r. ss. }
    unfold mrec.
    assert(TRANSL: simg eq (Ordinal.from_nat 100)
                        (x0 <- interp_Es (ModSem.prog ms_src)
                                         ((ModSem.prog ms_src) _ (Call "main" (Any.upcast tt))) st_src0;; Ret (snd x0))
                        (x0 <- interp_Es (ModSem.prog ms_src)
                                         (interp_hCallE_src (trigger (hCall "main" (Any.upcast tt)))) st_src0;; Ret (snd x0))).
    { clear SIM. unfold interp_hCallE_src. rewrite unfold_interp. ss. cbn. rewrite interp_Es_bind. rewrite interp_Es_callE.
      igo.
      pfold. econs; eauto.
      { instantiate (1:= Ordinal.from_nat 99). admit "ez". }
      left.
      replace (Ordinal.from_nat 99) with (Ordinal.add (Ordinal.from_nat 50) (Ordinal.from_nat 49)) by admit "ez".
      eapply simg_bind with (RR:=eq).
      - eapply simg_refl; et.
      - ii. des_ifs. ss. rewrite interp_Es_tau. igo.
        pfold. econs; eauto.
        { instantiate (1:= Ordinal.from_nat 49). admit "ez". }
        left. rewrite interp_Es_ret. igo. ss. eapply simg_refl; et.
    }
    assert(TRANSR: simg eq (Ordinal.from_nat 100)
                        (x0 <- interp_Es (ModSem.prog ms_tgt)
                                         (interp_hCallE_tgt stb "Main" (trigger (hCall "main" (Any.upcast tt)))) st_tgt0;; Ret (snd x0))
                        (x0 <- interp_Es (ModSem.prog ms_tgt)
                                         ((ModSem.prog ms_tgt) _ (Call "main" (Any.upcast tt))) st_tgt0;; Ret (snd x0))).
    { clear SIM. unfold interp_hCallE_tgt. rewrite unfold_interp. ss.
      cbn. rewrite interp_Es_bind. igo. des_ifs. ss.
      unfold HoareCall. rewrite ! interp_Es_bind. igo.
      rewrite ! interp_Es_eventE. igo.
      pfold. econs; eauto.
      { instantiate (1:= Ordinal.from_nat 99). admit "ez". }
      eexists ((fst st_tgt0) "Main", ε). igo. left.
      pfold. econs; eauto.
      { instantiate (1:= Ordinal.from_nat 98). admit "ez". }
      left.
      pfold. econs; eauto.
      { instantiate (1:= Ordinal.from_nat 97). admit "ez". }
      left.
      rewrite ! interp_Es_bind. igo. rewrite ! interp_Es_rE. igo.
      ss. fold ms_tgt.
      des_ifs; cycle 1.
      { admit "ez - use WF1". }
      destruct p.
      assert(s = "Main") by admit "ez". clarify. ss.
      replace (update
                      (fun mn0 : string =>
                       match find (fun mnr : string * Σ => dec mn0 (fst mnr)) (ModSem.initial_mrs ms_tgt) with
                       | Some r => snd r
                       | None => ε
                       end) "Main" c, [ε]) with st_tgt0; cycle 1.
      { unfold st_tgt0. fold ms_tgt.
        unfold ModSem.initial_r_state. f_equal. apply func_ext. i. unfold update. des_ifs; ss; clarify. }
      unfold guarantee. igo. pfold. econs; et.
      { instantiate (1:= Ordinal.from_nat 96). admit "ez". }
      esplits; eauto.
      { unfold ε. rewrite ! URA.unit_id. eapply URA.extends_updatable. rr. esplits; eauto. rewrite ! URA.unit_id. ss. }
      left.
      pfold. econs; eauto.
      { instantiate (1:= Ordinal.from_nat 95). admit "ez". }
      left.
      pfold. econs; eauto.
      { instantiate (1:= Ordinal.from_nat 94). admit "ez". }
      left.
      rewrite ! interp_Es_bind. igo. rewrite interp_Es_eventE. igo.
      pfold. econs; eauto.
      { instantiate (1:= Ordinal.from_nat 93). admit "ez". }
      eexists ε. left. igo. pfold. econs; et.
      { instantiate (1:= Ordinal.from_nat 92). admit "ez". }
      left. pfold. econs; et.
      { instantiate (1:= Ordinal.from_nat 91). admit "ez". }
      left.
      rewrite interp_Es_bind. igo. rewrite interp_Es_rE. ss. igo.
      fold ms_tgt.
      replace (fun mn0 => match find (fun mnr => dec mn0 (fst mnr)) (ModSem.initial_mrs ms_tgt)
                          with
                          | Some r0 => snd r0
                          | None => ε
                          end) with (fst st_tgt0); cycle 1.
      { unfold st_tgt0. ss. }
      pfold. econs; et.
      { instantiate (1:= Ordinal.from_nat 90). admit "ez". }
      eexists ε. left. igo. pfold. unfold guarantee. igo. econs; eauto.
      { instantiate (1:= Ordinal.from_nat 89). admit "ez". }
      esplits; eauto.
      { unfold ε. rewrite ! URA.unit_id. ss. }
      left. pfold. econs; et.
      { instantiate (1:= Ordinal.from_nat 88). admit "ez". }
      left. pfold. econs; et.
      { instantiate (1:= Ordinal.from_nat 87). admit "ez". }
      rewrite interp_Es_bind. igo. rewrite interp_Es_eventE. igo.
      left. pfold. econs; et.
      { instantiate (1:= Ordinal.from_nat 86). admit "ez". }
      eexists tt; eauto.
      igo.
      left. pfold. econs; et.
      { instantiate (1:= Ordinal.from_nat 85). admit "ez". }
      left. pfold. econs; et.
      { instantiate (1:= Ordinal.from_nat 84). admit "ez". }
      rewrite interp_Es_bind. igo. rewrite interp_Es_eventE. igo.
      left. pfold. econs; et.
      { instantiate (1:= Ordinal.from_nat 83). admit "ez". }
      exists I; eauto. igo. left. pfold. econs; et.
      { instantiate (1:= Ordinal.from_nat 82). admit "ez". }
      left. pfold. econs; et.
      { instantiate (1:= Ordinal.from_nat 81). admit "ez". }
      rewrite interp_Es_bind. igo.
      left.
      replace (Ordinal.from_nat 81) with (Ordinal.add (Ordinal.from_nat 41) (Ordinal.from_nat 40)) by admit "ez".
      eapply simg_bind with (RR:=eq).
      - rewrite interp_Es_callE.
        pfold. econs; et.
        { instantiate (1:= Ordinal.from_nat 39). admit "ez". }
        left.
        replace st_tgt0 with (fst st_tgt0, [ε]); cycle 1.
        { ss. }
        eapply simg_refl; ss.
      - ii. des_ifs. ss. rewrite interp_Es_bind. igo.
        rewrite interp_Es_rE. igo. unfold ModSem.handle_rE. des_ifs.
        { admit "we should use stronger RR, not eq; we should know that stackframe is not popped (unary property)". }
        unfold assume. igo.
        pfold. econs; eauto.
        { instantiate (1:= Ordinal.from_nat 40). admit "ez". }
        ii. left. pfold. econs; eauto.
        { instantiate (1:= Ordinal.from_nat 39). admit "ez". }
        left. pfold. econs; eauto.
        { instantiate (1:= Ordinal.from_nat 38). admit "ez". }
        rewrite interp_Es_bind. igo. rewrite interp_Es_eventE. igo.
        left. pfold. econs; eauto.
        { instantiate (1:= Ordinal.from_nat 37). admit "ez". }
        ii. igo.
        left. pfold. econs; eauto.
        { instantiate (1:= Ordinal.from_nat 36). admit "ez". }
        left. pfold. econs; eauto.
        { instantiate (1:= Ordinal.from_nat 35). admit "ez". }
        rewrite interp_Es_bind. igo. rewrite interp_Es_rE. igo. ss. igo.
        left. pfold. econs; eauto.
        { instantiate (1:= Ordinal.from_nat 34). admit "ez". }
        left. pfold. econs; eauto.
        { instantiate (1:= Ordinal.from_nat 33). admit "ez". }
        rewrite interp_Es_bind. igo. rewrite interp_Es_eventE. igo.
        left. pfold. econs; eauto.
        { instantiate (1:= Ordinal.from_nat 32). admit "ez". }
        ii.
        igo.
        left. pfold. econs; eauto.
        { instantiate (1:= Ordinal.from_nat 31). admit "ez". }
        left. pfold. econs; eauto.
        { instantiate (1:= Ordinal.from_nat 30). admit "ez". }
        rewrite interp_Es_ret. igo. rewrite interp_Es_tau. igo.
        left. pfold. econs; eauto.
        { instantiate (1:= Ordinal.from_nat 29). admit "ez". }
        rewrite interp_Es_ret. igo. ss.
        left. eapply simg_refl; ss.
    }

    replace (x0 <- interp_Es (ModSem.prog ms_src) ((ModSem.prog ms_src) _ (Call "main" (Any.upcast tt))) st_src0;; Ret (snd x0)) with
        (x0 <- interp_Es (ModSem.prog ms_src) (interp_hCallE_src (trigger (hCall "main" (Any.upcast tt)))) st_src0;; Ret (snd x0)); cycle 1.
    { admit "hard -- by transitivity". }
    replace (x0 <- interp_Es (ModSem.prog ms_tgt) ((ModSem.prog ms_tgt) _ (Call "main" (Any.upcast tt))) st_tgt0;; Ret (snd x0)) with
        (x0 <- interp_Es (ModSem.prog ms_tgt) (interp_hCallE_tgt stb "Main" (trigger (hCall "main" (Any.upcast tt)))) st_tgt0;; Ret (snd x0)); cycle 1.
    { admit "hard -- by transitivity". }
    replace (Ordinal.from_nat 98) with (Ordinal.add (Ordinal.from_nat 100) (Ordinal.from_nat 100)); cycle 1.
    { admit "ez". }
    fold simg.
    eapply simg_bind.
    - eapply adequacy_type_aux; ss. subst st_src0 st_tgt0. ss.
    - ii. ss. des_ifs. des; ss. clarify. pfold. econs; eauto.
  Qed.

End CANCEL.
