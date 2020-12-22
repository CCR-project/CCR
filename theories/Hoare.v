Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



(***
r <- Take;;
FAdd(r);; <-------------------------- illegal in some sense
assume((blk |-> R) <= r \/ (blk |-> G) <= r \/ (blk |-> B) <= r);;  (iProp???)
meta-assume(list mname(for modular reasoning), current stackframe);;

r <- Choose;;
FSub(r);; := Get;; Choose;; guarantee;; Set;;
guarantee(blk |-> v <= r);;
(call f);;
r <- Take;;
FAdd(r);; <-------------------------- illegal in some sense
assume(some_other_resource <= r);;
meta-assume(list mname(for modular reasoning), current stackframe);;

r <- Choose;;
FSub(r);;
guarantee(blk |-> v <= r);;
***)

(***
HoareFun := FPush;; [[boilerplate]] real_code [[boilerplate]] FPop;;
real_code := itree, using HoareCall, not benign call
             calling meta-assume is allowed. "list mname" is hard-coded in the module.
HoareCall := [[boilerplate]] call [[boilerplate]]

the illegal update (FAdd(r)) is only allowed in boilerplate code.
FPush/FPop is only allowed in boilerplate code.
***)

(***
FPush
  r <- Take;
  assume(P /\ IP r);
  cur <- FGet; FPut (cur * r);



    r <- Choose;
    guarantee(P /\ IP r);
    cur <- FGet; cur' <- Choose; guarantee(cur' * r = cur); FPut cur';
      call;
    ...
    ...
    ...

  ...
  ...
  ...
FPop

NB: this "discarded" resource is *actually* discarded; the user can't access it in the real_code
***)

(***
Where does the `Function Locality` appear in our scenario?
Use Rely/Guarantee in simulation technique.



FPush
  r <- Take;
  assume(P /\ IP r);
  cur <- FGet; FPut (cur * r);



    r <- Choose;
    guarantee(P /\ IP r);
    cur <- FGet; cur' <- Choose; guarantee(cur' * r = cur); FPut cur';
      call;
    ...
    ...
    ...

  ...
  ...
  ...
FPop

***)
Section PROOF.
  (* Context {myRA} `{@GRA.inG myRA Σ}. *)
  Context {Σ: GRA.t}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.
  Variable mn: mname.
  Context `{X: Type}. (*** a meta-variable ***)

  (* Definition HoareFun *)
  (*            (I: URA.car -> Prop) *)
  (*            (P: URA.car -> list val -> Prop) *)
  (*            (Q: URA.car -> list val -> URA.car -> val -> Prop) *)
  (*            (f: list val -> itree Es val): *)
  (*   list val -> itree Es val := *)
  (*   fun varg => *)
  (*     rarg <- trigger (Take URA.car);; trigger (Forge rarg);; (*** virtual resource passing ***) *)
  (*     assume(P rarg varg);; (*** precondition ***) *)
  (*     mopen <- trigger (MGet mn);; assume(I mopen);; (*** opening the invariant ***) *)

  (*     vret <- f varg;; (*** body ***) *)

  (*     mclose <- trigger (MGet mn);; guarantee(I mclose);; (*** closing the invariant ***) *)
  (*     rret <- trigger (Choose URA.car);; guarantee(Q rarg varg rret vret);; (*** postcondition ***) *)
  (*     trigger (Discard rret);; (*** virtual resource passing ***) *)

  (*     Ret vret (*** return ***) *)
  (* . *)

  Definition HoareFun
             (P: X -> list val -> Σ -> Prop)
             (Q: X -> val -> Σ -> Prop)
             (body: list val -> itree Es val): list val -> itree Es val := fun varg =>
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
             (P: X -> list val -> Σ -> Prop)
             (Q: X -> val -> Σ -> Prop):
    fname -> list val -> itree Es val :=
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

  (* Definition HoareFunCanceled *)
  (*            (body: itree Es unit): list val -> itree Es val := fun varg => *)
  (*   body;; (*** "rudiment": we don't remove extcalls because of termination-sensitivity ***) *)
  (*   vret <- trigger (Choose _);; *)
  (*   Ret vret (*** return ***) *)
  (* . *)

  (* Definition HoareCallCanceled: *)
  (*   fname -> list val -> itree Es val := *)
  (*   fun fn varg => *)
  (*     vret <- trigger (Call fn varg);; (*** call ***) *)
  (*     Ret vret (*** return to body ***) *)
  (* . *)

  (* Section PLAYGROUND. *)

  (*   (*** Q can mention the resource in the P ***) *)
  (*   Let HoareFun_sophis *)
  (*              (mn: mname) *)
  (*              (P: URA.car -> Prop) *)
  (*              (Q: URA.car -> val -> URA.car -> Prop) *)
  (*              (f: itree Es unit): itree Es val := *)
  (*     rarg <- trigger (Take URA.car);; trigger (Forge rarg);; (*** virtual resource passing ***) *)
  (*     assume(P rarg);; (*** precondition ***) *)
  (*     mopen <- trigger (MGet mn);; *)

  (*     f;; (*** it is a "rudiment": we don't remove extcalls because of termination-sensitivity ***) *)
  (*     vret <- trigger (Choose _);; *)

  (*     mclose <- trigger (MGet mn);; *)
  (*     rret <- trigger (Choose URA.car);; trigger (Discard rret);; (*** virtual resource passing ***) *)
  (*     guarantee(Q rarg vret rret);; (*** postcondition ***) *)

  (*     Ret vret (*** return ***) *)
  (*   . *)

  (*   Let HoareFun_sophis2 *)
  (*              (mn: mname) *)
  (*              (P: URA.car -> Prop) *)
  (*              (Q: URA.car -> val -> URA.car -> Prop) *)
  (*              (f: itree Es unit): itree Es val := *)
  (*     _rarg_ <- trigger (Take _);; *)
  (*     HoareFun mn (P /1\ (eq _rarg_)) (Q _rarg_) f *)
  (*   . *)

  (* End PLAYGROUND. *)




  (* Definition HoareCall *)
  (*            (I: URA.car -> Prop) *)
  (*            (P: URA.car -> list val -> Prop) *)
  (*            (Q: URA.car -> list val -> URA.car -> val -> Prop): *)
  (*   fname -> list val -> itree Es val := *)
  (*   fun fn varg => *)
  (*     mclose <- trigger (MGet mn);; guarantee(I mclose);; (*** closing the invariant ***) *)
  (*     rarg <- trigger (Choose URA.car);; guarantee(P rarg varg);; (*** precondition ***) *)
  (*     trigger (Discard rarg);; (*** virtual resource passing ***) *)

  (*     vret <- trigger (Call fn varg);; (*** call ***) *)

  (*     rret <- trigger (Take URA.car);; trigger (Forge rret);; (*** virtual resource passing ***) *)
  (*     assume(Q rarg varg rret vret);; (*** postcondition ***) *)
  (*     mopen <- trigger (MGet mn);; assume(I mopen);; (*** opening the invariant ***) *)

  (*     Ret vret (*** return to body ***) *)
  (* . *)



  (* Definition HoareFun *)
  (*            (INV: URA.car -> Prop) *)
  (*            (P: URA.car -> list val -> Prop) *)
  (*            (Q: URA.car -> list val -> URA.car -> val -> Prop) *)
  (*            (f: list val -> itree Es val): *)
  (*   list val -> itree Es val := *)
  (*   fun vs0 => *)
  (*     ld0 <- trigger (MGet mn);; *)
  (*     r <- trigger (Take URA.car);; *)
  (*     assume(P ld0 r vs0);; *)
  (*     FAdd r;; *)

  (*     assume(<<WTY: URA.wf (URA.add ld0 r)>>);; *)
  (*     vr <- (f vs0);; *)

  (*     ld1 <- trigger (MGet mn);; *)
  (*     rr <- trigger (Choose URA.car);; *)
  (*     guarantee(Q ld0 r vs0 ld1 rr vr);; *)
  (*     FSub rr;; *)
  (*     Ret vr *)
  (* . *)

  (* Definition HoareCall *)
  (*            (P: URA.car -> URA.car -> list val -> Prop) *)
  (*            (Q: URA.car -> URA.car -> list val -> URA.car -> URA.car -> val -> Prop): *)
  (*   fname -> list val -> itree (callE +' mdE +' fnE +' eventE) val := *)
  (*   fun fn vs0 => *)
  (*     ld0 <- trigger (MGet mn);; *)
  (*     r <- trigger (Choose URA.car);; *)
  (*     FSub r;; *)
  (*     guarantee(P ld0 r vs0);; *)

  (*     vr <- trigger (Call fn vs0);; *)

  (*     Ret vr *)
  (* . *)

End PROOF.















Definition map_fst A0 A1 B (f: A0 -> A1): (A0 * B) -> (A1 * B) := fun '(a, b) => (f a, b).
Definition map_snd A B0 B1 (f: B0 -> B1): (A * B0) -> (A * B1) := fun '(a, b) => (a, f b).
(*** TODO: Move to Coqlib. TODO: Somehow use case_ ??? ***)

Section CANCEL.

  Context `{Σ: GRA.t}.

  Variant hCallE: Type -> Type :=
  | hCall
      (* (mn: mname) *)
      (* (P: list val -> Σ -> Prop) (Q: list val -> Σ -> val -> Σ -> Prop) *)
      (fn: fname) (varg: list val): hCallE val
  .

  (*** spec table ***)
  Record fspec: Type := mk {
    mn: mname;
    X: Type; (*** a meta-variable ***)
    precond: X -> list val -> Σ -> Prop;
    postcond: X -> val -> Σ -> Prop;
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

  Definition handle_hCallE_tgt: hCallE ~> itree Es :=
    fun _ '(hCall fn varg) =>
      match List.find (fun '(_fn, _) => dec fn _fn) stb with
      | Some (_, f) =>
        (HoareCall f.(mn) (f.(precond)) (f.(postcond)) fn varg)
      | None => triggerNB
      end
  .

  Definition interp_hCallE_tgt: itree (hCallE +' eventE) ~> itree Es :=
    interp (case_ (bif:=sum1) handle_hCallE_tgt
                  ((fun T X => trigger X): eventE ~> itree Es))
  .

  Definition body_to_tgt (body: list val -> itree (hCallE +' eventE) val): list val -> itree Es val :=
    fun varg => interp_hCallE_tgt (body varg)
  .



  Definition handle_hCallE_src: hCallE ~> itree Es :=
    fun _ '(hCall fn varg) => trigger (Call fn varg)
  .

  Definition interp_hCallE_src: itree (hCallE +' eventE) ~> itree Es :=
    interp (case_ (bif:=sum1) handle_hCallE_src
                  ((fun T X => trigger X): eventE ~> itree Es))
  .

  Definition body_to_src (body: list val -> itree (hCallE +' eventE) val): list val -> itree Es val :=
    fun varg => interp_hCallE_src (body varg)
  .
  Definition fun_to_tgt (fn: fname) (body: list val -> itree (hCallE +' eventE) val): (list val -> itree Es val) :=
    match List.find (fun '(_fn, _) => dec fn _fn) stb with
    | Some (_, fs) => HoareFun fs.(mn) (fs.(precond)) (fs.(postcond)) (body_to_tgt body)
    | _ => fun _ => triggerNB
    end.
  Definition fun_to_src (body: list val -> itree (hCallE +' eventE) val): (list val -> itree Es val) :=
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
  Variable ftb: list (fname * (list val -> itree (hCallE +' eventE) val)).
  Hypothesis WTY: ms_tgt.(ModSem.fnsems) = List.map (fun '(fn, body) => (fn, fun_to_tgt stb fn body)) ftb.

  Definition ms_src: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_src body)) ftb;
    (* ModSem.initial_mrs := List.map (map_snd (fun _ => ε)) ms_tgt.(ModSem.initial_mrs); *)
    ModSem.initial_mrs := [];
    (*** note: we don't use resources, so making everything as a unit ***)
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

  (* Variable match_states: state (Mod.interp md_tgt) -> state (Mod.interp md_tgt) -> Prop. *)

  (* Let adequacy_type_aux *)
  (*     st_src0 st_tgt0 *)
  (*     (SIM: match_states st_src0 st_tgt0) *)
  (*   : *)
  (*     Beh.of_state (Mod.interp md_tgt) st_tgt0 <1= Beh.of_state (Mod.interp md_tgt) st_src0 *)
  (* . *)
  (* Proof. *)
  (*   revert_until match_states. pcofix CIH. i. punfold PR. *)
  (*   inv PR. *)
  (*   - ss. *)
  (* Qed. *)
  Lemma interp_state_bind:
  forall (E F : Type -> Type) (A B S : Type) (f : forall T : Type, E T -> S -> itree F (S * T)) (t : itree E A)
    (k : A -> itree E B) (s : S),
  interp_state f (` x : _ <- t;; k x) s = ` st : S * A <- interp_state f t s;; interp_state f (k (snd st)) (fst st)
  .
  Proof. i. f. apply interp_state_bind. Qed.

  Lemma interp_state_vis:
  forall (E F : Type -> Type) (S T U : Type) (e : E T) (k : T -> itree E U) (h : forall T0 : Type, E T0 -> stateT S (itree F) T0)
    (s : S), interp_state h (Vis e k) s = ` sx : S * T <- h T e s;; (tau;; interp_state h (k (snd sx)) (fst sx))
  .
  Proof.
    i. f. apply interp_state_vis.
  Qed.

  Lemma interp_state_tau :
    forall (E F : Type -> Type) (S T : Type) (t : itree E T) (h : forall T0 : Type, E T0 -> stateT S (itree F) T0) (s : S),
      interp_state h (tau;; t) s = (tau;; interp_state h t s)
  .
  Proof.
    i. f. apply interp_state_tau.
  Qed.

  Lemma interp_state_ret:
  forall (E F : Type -> Type) (R S : Type) (f : forall T : Type, E T -> S -> itree F (S * T)) (s : S) (r : R),
  interp_state f (Ret r) s = Ret (s, r)
  .
  Proof.
    i. f. apply interp_state_ret.
  Qed.

  Lemma unfold_interp:
    forall (E F : Type -> Type) (R : Type) (f : forall T : Type, E T -> itree F T) (t : itree E R),
      interp f t = _interp f (observe t)
  .
  Proof.
    i. f. apply unfold_interp.
  Qed.
  Lemma interp_ret:
    forall (E F : Type -> Type) (R : Type) (f : forall T : Type, E T -> itree F T) (x : R), interp f (Ret x) = Ret x.
  Proof. i. f. apply interp_ret. Qed.

  Definition my_interp A (prog: callE ~> itree Es) (itr0: itree Es A) (st0: ModSem.r_state) :=
    ModSem.interp_rE (interp_mrec prog itr0) st0
  .

  Ltac grind := repeat (f_equiv; try apply func_ext; ii; try (des_ifs; check_safe)).

  Lemma my_interp_bind
        (prog: callE ~> itree Es)
        A B
        (itr: itree Es A) (ktr: A -> itree Es B)
        st0
    :
      my_interp prog (v <- itr ;; ktr v) st0 =
      '(st1, v) <- my_interp prog (itr) st0 ;; my_interp prog (ktr v) st1
  .
  Proof.
    unfold my_interp.
    unfold ModSem.interp_rE.
    rewrite interp_mrec_bind.
    rewrite interp_state_bind.
    grind.
  Qed.

  Lemma my_interp_ret
        T
        prog st0 (v: T)
    :
      my_interp prog (Ret v) st0 = Ret (st0, v)
  .
  Proof.
    unfold my_interp. unfold ModSem.interp_rE.
    rewrite unfold_interp_mrec. ss.
    rewrite interp_state_ret. ss.
  Qed.

  Lemma interp_mrec_hit:
    forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) (U : Type) (a : D U),
      interp_mrec ctx (trigger a) = (tau;; interp_mrec ctx (ctx _ a))
  .
  Proof.
    i. rewrite unfold_interp_mrec. ss.
    unfold resum, ReSum_id, id_, Id_IFun. rewrite bind_ret_r. ss.
  Qed.


  Definition tauK {E R}: R -> itree E R := fun r => tau;; Ret r.
  Hint Unfold tauK.

  (*** TODO: I don't want "F" here, but it is technically needed. Report it to itree people? ***)
  Lemma interp_mrec_miss:
    (* forall (D E F: Type -> Type) `{F -< E} (ctx : forall T : Type, D T -> itree (D +' E) T) (U : Type) (a : F U), *)
    forall (D E F: Type -> Type) `{F -< E} (ctx : forall T : Type, D T -> itree (D +' E) T) (U : Type) (a : F U),
      interp_mrec ctx (trigger a) = x <- (trigger a);; tau;; Ret x
      (* (trigger a) >>= tauK *)
  .
  Proof.
    i. rewrite unfold_interp_mrec. cbn.
    unfold trigger. irw.
    grind. irw. ss.
  Qed.

  (*** TODO: interp_trigger_eqit does not exist. report to itree people? ***)
  Lemma interp_state_trigger:
  forall (E F : Type -> Type) (R S : Type) (e : E R) (f : forall T : Type, E T -> stateT S (itree F) T) (s : S),
  interp_state f (ITree.trigger e) s = ` x : S * R <- f R e s;; (tau;; Ret x)
  .
  Proof. i. f. apply interp_state_trigger_eqit. Qed.

  Lemma my_interp_callE
        p st0
        (* (e: Es Σ) *)
        (e: callE val)
    :
      my_interp p (trigger e) st0 = tau;; (my_interp p (p val e) st0)
  .
  Proof.
    unfold my_interp. unfold ModSem.interp_rE. rewrite interp_mrec_hit. cbn.
    rewrite interp_state_tau. grind.
  Qed.

  Lemma my_interp_rE
        p st0
        (* (e: Es Σ) *)
        T
        (e: rE T)
    :
      my_interp p (trigger e) st0 =
      '(st1, r) <- ModSem.handle_rE e st0;;
      tau;; tau;;
      Ret (st1, r)
      (* interp_state (case_ ModSem.handle_rE pure_state) (tau;; Ret r) st1 *)
  .
  Proof.
    unfold my_interp. unfold ModSem.interp_rE.
    (* rewrite unfold_interp_mrec. cbn. *)
    unfold Es.
    rewrite interp_mrec_miss with (D:=callE) (E:=rE +' eventE) (F:=rE) (a:=e).
    rewrite interp_state_bind.
    rewrite interp_state_trigger. irw. grind. irw. grind.
    rewrite interp_state_tau. grind.
    rewrite interp_state_ret. ss.
  Qed.

  Lemma my_interp_eventE
        p st0
        (* (e: Es Σ) *)
        T
        (e: eventE T)
    :
      my_interp p (trigger e) st0 = r <- trigger e;; tau;; tau;; Ret (st0, r)
  .
  Proof.
    unfold my_interp. unfold ModSem.interp_rE.
    (* rewrite unfold_interp_mrec. cbn. *)
    unfold Es.
    rewrite interp_mrec_miss with (D:=callE) (E:=rE +' eventE) (F:=eventE) (a:=e).
    rewrite interp_state_bind.
    rewrite interp_state_trigger. irw. unfold pure_state.
    unfold resum, ReSum_id, id_, Id_IFun.
    irw. grind. irw. grind.
    rewrite interp_state_tau. grind.
    rewrite interp_state_ret. ss.
  Qed.

  Lemma my_interp_triggerUB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (my_interp prog (triggerUB) st0: itree eventE (_ * A)) = triggerUB
  .
  Proof.
    unfold triggerUB. rewrite my_interp_bind. rewrite my_interp_eventE.
    irw. grind.
  Qed.

  Lemma my_interp_triggerNB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (my_interp prog (triggerNB) st0: itree eventE (_ * A)) = triggerNB
  .
  Proof.
    unfold triggerNB. rewrite my_interp_bind. rewrite my_interp_eventE.
    irw. grind.
  Qed.

  Ltac igo := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r; try rewrite bind_tau;
                      try rewrite interp_vis;
                      try rewrite interp_ret;
                      try rewrite interp_tau;
                      try rewrite interp_trigger
                     ).

  Let W: Type := ((string -> Σ) * list Σ).
  Let wf: W -> W -> Prop :=
    fun '(mrs_src, frs_src) '(mrs_tgt, frs_tgt) =>
      (<<LEN: List.length frs_src = List.length frs_tgt>>) /\
      (<<WFTGT: URA.wf (URA.add (fold_left URA.add (List.map (mrs_tgt <*> fst) ms_tgt.(ModSem.initial_mrs)) ε)
                                (fold_left URA.add frs_tgt ε))>>)
  .

  Hypothesis WTB: List.map fst ftb = List.map fst stb.

  Let adequacy_type_aux:
    let p_src: callE ~> itree Es := fun _ ce => trigger PushFrame;; rv <- ModSem.sem ms_src ce;; trigger PopFrame;; Ret rv in
    let p_tgt: callE ~> itree Es := fun _ ce => trigger PushFrame;; rv <- ModSem.sem ms_tgt ce;; trigger PopFrame;; Ret rv in
    forall st_src0 st_tgt0 (SIM: wf st_src0 st_tgt0) (ce: hCallE val),
    sim (Mod.interp md_src) (Mod.interp md_tgt) lt 100%nat
        (* ('(st_src1, r) <- (my_interp p_src (interp_hCallE_src (trigger ce)) st_src0);; Ret r) *)
        (* ('(st_tgt1, r) <- (my_interp p_tgt (interp_hCallE_tgt stb (trigger ce)) st_tgt0);; Ret r) *)
        (x <- (my_interp p_src (interp_hCallE_src (trigger ce)) st_src0);; Ret (snd x))
        (x <- (my_interp p_tgt (interp_hCallE_tgt stb (trigger ce)) st_tgt0);; Ret (snd x))
  .
  Proof.
    intros ? ?.
    pcofix CIH. i. pfold.
    dependent destruction ce.
    Local Opaque GRA.to_URA.
    ss.
    unfold interp_hCallE_src.
    unfold interp_hCallE_tgt.
    rewrite ! unfold_interp. ss.
    rewrite ! my_interp_bind. igo. cbn.
    unfold handle_hCallE_src at 2. unfold handle_hCallE_tgt at 2. des_ifs. igo.
    rewrite ! interp_ret.
    unfold p_src at 2. unfold p_tgt at 2. ss. igo.
    rewrite ! my_interp_bind. igo.
    rewrite ! my_interp_rE.
    unfold ModSem.handle_rE.
    r in SIM. des_ifs_safe. des.
    des_ifs.
    { (*** tgt NB ***) irw. unfold triggerNB. irw. eapply sim_demonic_tgt; ss. ii. inv STEP; ss. }
    irw.
    Ltac tauLR := eapply sim_demonic_both; ss; intros ? STEP; inv STEP; esplits; et; [econs; ss; et|].
    tauLR. left; pfold.
    tauLR. left; pfold.
    unfold unwrapU.
    destruct (find _ (List.map (fun '(fn0, body) => (fn0, fun_to_src body)) ftb)) eqn:FIND; cycle 1.
    { rewrite my_interp_bind. rewrite my_interp_triggerUB. irw.
      (*** src UB ***) unfold triggerUB. irw. eapply sim_angelic_src; ss. ii. inv STEP; ss.
    }
    fold ms_tgt. rewrite WTY.
    rewrite find_map in FIND. uo. des_ifs_safe.
    rename Heq into FS.
    unfold Basics.compose in *.
    rewrite find_map. uo. des_ifs; cycle 1; rename Heq0 into FT.
    { exfalso.
      unfold Basics.compose in *.
      eapply find_some in FS. des; ss.
      eapply find_none in FT; et. des_ifs. ss.
      clarify.
    }
    igo.
    rewrite ! my_interp_bind.
    igo.
    unfold fun_to_src, body_to_src.
    unfold fun_to_tgt, body_to_tgt.
    des_ifs; cycle 1.
    { irw. ss. admit "ez - use FT, WTB. We should refactor -- e.g., to use alist, and then use find as a map. this is too low lv".
    }
    unfold HoareFun.

  Qed.
      (p_src:
  p_src := fun (H : Type) (ce : callE H) => trigger PushFrame;; ` rv : H <- ModSem.sem ms_src ce;; trigger PopFrame;; Ret rv
   : forall H : Type, callE H -> itree Es H
  p_tgt := fun (H : Type) (ce : callE H) =>
           trigger PushFrame;;
           ` rv : H <- ModSem.sem (Mod.get_modsem md_tgt (Sk.load_skenv (Mod.sk md_tgt))) ce;; trigger PopFrame;; Ret rv
   : forall H : Type, callE H -> itree Es H
  st_src0, st_tgt0 : ModSem.r_state
  SIM : wf st_src0 st_tgt0
  ce : callE val
  ============================
  paco3 (_sim (Mod.interp md_src) (Mod.interp md_tgt) lt) bot3 100%nat
    (` x : ModSem.r_state * val <- ModSem.interp_rE (mrec p_src ce) st_src0;; Ret (snd x))
    (` x : ModSem.r_state * val <- ModSem.interp_rE (mrec p_tgt ce) st_tgt0;; Ret (snd x))

  Theorem adequacy_type: Beh.of_program (Mod.interp md_tgt) <1= Beh.of_program (Mod.interp md_src).
  Proof.
    eapply adequacy.
    { apply lt_wf. }
    econs.
    { apply lt_wf. }
    eexists 102%nat.
    ss.
    set (fun _ ce => trigger PushFrame;; rv <- ModSem.sem ms_src ce;; trigger PopFrame;; Ret rv) as p_src.
    set (fun _ ce  =>
              trigger PushFrame;;
              rv <- ModSem.sem (Mod.get_modsem md_tgt (Sk.load_skenv (Mod.sk md_tgt))) ce;;
              trigger PopFrame;; Ret rv) as p_tgt.
    unfold ITree.map.
    unfold assume.
    igo.
    pfold. eapply sim_angelic_src; ss. ii. inv STEP; ss; irw in H0; csc. clear_tac. esplits; et. left.
    pfold. eapply sim_angelic_tgt; ss. esplits; et. { irw. econs. } left.
    set (st_src0 := (ModSem.initial_r_state ms_src)).
    set (st_tgt0 := (ModSem.initial_r_state (Mod.get_modsem md_tgt (Sk.load_skenv (Mod.sk md_tgt))))).
    assert(SIM: wf st_src0 st_tgt0).
    { r. ss. esplits; et. admit "initial wf: mandate this to the user". }
    clearbody st_src0 st_tgt0.
    clear x.
    abstr (Call "main" []) ce.
    unfold mrec.
    replace (ModSem.interp_rE (interp_mrec p_src (p_src val ce)) st_src0) with
        (my_interp p_src (p_src val ce) st_src0) by ss.
    replace (ModSem.interp_rE (interp_mrec p_tgt (p_tgt val ce)) st_tgt0) with
        (my_interp p_tgt (p_tgt val ce) st_tgt0) by ss.
    (* unfold ModSem.interp_rE. *)
    (* unfold mrec. *)
    revert_until p_tgt.
    pcofix CIH. i. pfold.
    dependent destruction ce.
    unfold p_src at 2. unfold p_tgt at 2. ss. igo.
    rewrite ! my_interp_bind. igo.
    rewrite ! my_interp_rE.
    unfold ModSem.handle_rE.
    r in SIM. des_ifs_safe. des.
    des_ifs.
    { (*** tgt NB ***) irw. unfold triggerNB. irw. eapply sim_demonic_tgt; ss. ii. inv STEP; ss. }
    irw.
    Ltac tauLR := eapply sim_demonic_both; ss; intros ? STEP; inv STEP; esplits; et; [econs; ss; et|].
    tauLR. left; pfold.
    tauLR. left; pfold.
    unfold unwrapU.
    destruct (find _ (List.map (fun '(fn0, body) => (fn0, fun_to_src body)) ftb)) eqn:FIND; cycle 1.
    { rewrite my_interp_bind. rewrite my_interp_triggerUB. irw.
      (*** src UB ***) unfold triggerUB. irw. eapply sim_angelic_src; ss. ii. inv STEP; ss.
    }
    fold ms_tgt. rewrite WTY.
    rewrite find_map in FIND. uo. des_ifs_safe.
    rename Heq into FS.
    unfold Basics.compose in *.
    rewrite find_map. uo. des_ifs; cycle 1; rename Heq0 into FT.
    { exfalso.
      unfold Basics.compose in *.
      eapply find_some in FS. des; ss.
      eapply find_none in FT; et. des_ifs. ss.
      clarify.
    }
    igo.
    rewrite ! my_interp_bind.
    igo.
    unfold fun_to_src, body_to_src.
    unfold fun_to_tgt, body_to_tgt.
    des_ifs; cycle 1.
    { irw. ss. admit "ez - use FT, WTB. We should refactor -- e.g., to use alist, and then use find as a map. this is too low lv".
    }
    unfold HoareFun.

    TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT

    rewrite my_interp_ret.
    des_ifs.
    irw.
    econs; et.
    ss.
    rewrite ! interp_mrec_bind.
    rewrite ! interp_state-bind.
    ss.


    destruct ce.
    




    pfold.
    pfold.
    clear x.
    assert(SIMST: (ModSem.initial_r_state ms_src) = 
    revert_until itr0_tgt.
    pcofix CIH.
    pfold.
    set (fun _ ce => trigger PushFrame;; rv <- ModSem.sem ms_tgt ce;; trigger PopFrame;; Ret rv) as itr0_tgt.
    set (mrec
             (fun (T : Type) (ce : callE T) =>
              trigger PushFrame;;
              ` rv : T <- ModSem.sem (Mod.get_modsem md_tgt (Sk.load_skenv (Mod.sk md_tgt))) ce;; trigger PopFrame;; Ret rv)
             (Call "main" []))
    ss.
    admit "In the proof, we will need to show
(1) Choose/Take cancel
(2) assume/guarantee cancel
(3) src is resource unaware
(4) tgt is always wf (so CheckWf always succeeds)
".
  Qed.

End CANCEL.
