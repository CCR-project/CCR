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


Inductive ord: Type :=
| ord_pure (n: nat)
| ord_top
.

Definition is_pure (o: ord): bool := match o with | ord_pure _ => true | _ => false end.

Definition ord_lt (next cur: ord): Prop :=
  match next, cur with
  | ord_pure next, ord_pure cur => (next < cur)%nat
  | _, ord_top => True
  | _, _ => False
  end
.

(**
(defface hi-light-green-b
  '((((min-colors 88)) (:weight bold :foreground "dark magenta"))
    (t (:weight bold :foreground "dark magenta")))
  "Face for hi-lock mode."
  :group 'hi-lock-faces)

 **)


Section PSEUDOTYPING.

(*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)

Section PROOF.
  (* Context {myRA} `{@GRA.inG myRA Σ}. *)
  Context {Σ: GRA.t}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.
  Variable mn: mname.
  Context {X Y Z: Type}.

  Definition HoareCall
             (tbr: bool)
             (ord_cur: ord)
             (P: X -> Y -> Any_tgt -> Σ -> ord -> Prop)
             (Q: X -> Z -> Any_tgt -> Σ -> Prop):
    gname -> Y -> itree Es Z :=
    fun fn varg_src =>
      '(marg, farg) <- trigger (Choose _);; put mn marg farg;; (*** updating resources in an abstract way ***)
      rarg <- trigger (Choose Σ);; discard rarg;; (*** virtual resource passing ***)
      x <- trigger (Choose X);; varg_tgt <- trigger (Choose Any_tgt);;
      ord_next <- trigger (Choose _);;
      guarantee(P x varg_src varg_tgt rarg ord_next);; (*** precondition ***)

      guarantee(ord_lt ord_next ord_cur /\ (tbr = true -> is_pure ord_next) /\ (tbr = false -> ord_next = ord_top));;
      vret_tgt <- trigger (Call fn varg_tgt);; (*** call ***)
      checkWf mn;;

      rret <- trigger (Take Σ);; forge rret;; (*** virtual resource passing ***)
      vret_src <- trigger (Take Z);;
      assume(Q x vret_src vret_tgt rret);; (*** postcondition ***)

      Ret vret_src (*** return to body ***)
  .

End PROOF.















(*** TODO: Move to Coqlib. TODO: Somehow use case_ ??? ***)
(* Definition map_fst A0 A1 B (f: A0 -> A1): (A0 * B) -> (A1 * B) := fun '(a, b) => (f a, b). *)
(* Definition map_snd A B0 B1 (f: B0 -> B1): (A * B0) -> (A * B1) := fun '(a, b) => (a, f b). *)

Variant hCallE: Type -> Type :=
| hCall (tbr: bool) (fn: gname) (varg_src: Any_src): hCallE Any_src
(*** tbr == to be removed ***)
.

Notation Es' := (hCallE +' pE +' eventE).

Fixpoint _APC (n: nat): itree Es' unit :=
  match n with
  | 0 => Ret tt
  | S n =>
    '(fn, varg) <- trigger (Choose _);;
    trigger (hCall true fn varg);;
    _APC n
  end.

Definition APC: itree Es' unit :=
  n <- trigger (Choose _);; _APC n
.





Section CANCEL.

  Context `{Σ: GRA.t}.

  (*** spec table ***)
  Record fspec: Type := mk {
    mn: mname;
    X: Type; (*** a meta-variable ***)
    AA: Type;
    AR: Type;
    precond: X -> AA -> Any_tgt -> Σ -> ord -> Prop; (*** meta-variable -> new logical arg -> current logical arg -> resource arg -> Prop ***)
    postcond: X -> AR -> Any_tgt -> Σ -> Prop; (*** meta-variable -> new logical ret -> current logical ret -> resource ret -> Prop ***)
  }
  .

  Record fspecbody: Type := mk_specbody {
    fsb_fspec:> fspec;
    fsb_body: fsb_fspec.(AA) -> itree (hCallE +' pE +' eventE) fsb_fspec.(AR);
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
    fun _ '(hCall tbr fn varg_src) =>
      match tbr with
      | true => trigger (Choose _)
      | false => trigger (Call fn varg_src)
      end
  .

  Definition interp_hCallE_src `{E -< Es}: itree (hCallE +' E) ~> itree Es :=
    interp (case_ (bif:=sum1) (handle_hCallE_src)
                  ((fun T X => trigger X): E ~> itree Es))
  .

  Definition body_to_src {AA AR} (body: AA -> itree (hCallE +' pE +' eventE) AR): AA -> itree Es AR :=
    fun varg_src => interp_hCallE_src (body varg_src)
  .

  Definition fun_to_src {AA AR} (body: AA -> itree (hCallE +' pE +' eventE) AR): (Any_src -> itree Es Any_src) :=
    cfun (body_to_src body)
  .





  Definition handle_hCallE_mid (ord_cur: ord): hCallE ~> itree Es :=
    fun _ '(hCall tbr fn varg_src) =>
      ord_next <- (if tbr then trigger (Choose _) else Ret ord_top);;
      guarantee(ord_lt ord_next ord_cur);;
      let varg_mid: Any_mid := (Any.pair ord_next↑ varg_src) in
      trigger (Call fn varg_mid)
  .

  Definition interp_hCallE_mid `{E -< Es} (ord_cur: ord): itree (hCallE +' E) ~> itree Es :=
    interp (case_ (bif:=sum1) (handle_hCallE_mid ord_cur)
                  ((fun T X => trigger X): E ~> itree Es))
  .

  Definition body_to_mid {AA AR} (ord_cur: ord) (body: (AA) -> itree (hCallE +' pE +' eventE) AR): AA -> itree Es AR :=
    fun varg_mid => interp_hCallE_mid ord_cur (body varg_mid)
  .

  Definition fun_to_mid {AA AR} (body: AA -> itree (hCallE +' pE +' eventE) AR): (Any_mid -> itree Es Any_src) :=
    fun varg_mid =>
      '(ord_cur, varg_src) <- varg_mid↓ǃ;;
      vret_src <- match ord_cur with
                  | ord_pure n => (interp_hCallE_mid ord_cur APC);; trigger (Choose _)
                  | _ => (body_to_mid ord_cur body) varg_src
                  end;;
      Ret vret_src↑
  .





  Definition handle_hCallE_tgt (mn: mname) (ord_cur: ord): hCallE ~> itree Es :=
    fun _ '(hCall tbr fn varg_src) =>
      match List.find (fun '(_fn, _) => dec fn _fn) stb with
      | Some (_, f) =>
        varg_src <- varg_src↓ǃ;;
        vret_src <- (HoareCall (mn) tbr ord_cur (f.(precond)) (f.(postcond)) fn varg_src);;
        Ret vret_src↑
      | None => triggerNB
      end
  .

  Definition interp_hCallE_tgt `{E -< Es} (mn: mname) (ord_cur: ord): itree (hCallE +' E) ~> itree Es :=
    interp (case_ (bif:=sum1) (handle_hCallE_tgt mn ord_cur)
                  ((fun T X => trigger X): E ~> itree Es))
  .

  Definition body_to_tgt {AA AR} (mn: mname) (ord_cur: ord)
             (body: AA -> itree (hCallE +' pE +' eventE) AR): AA -> itree Es AR :=
    fun varg_tgt => interp_hCallE_tgt mn ord_cur (body varg_tgt)
  .

  Definition HoareFun
             (mn: mname)
             {X Y Z: Type}
             (P: X -> Y -> Any_tgt -> Σ -> ord -> Prop)
             (Q: X -> Z -> Any_tgt -> Σ -> Prop)
             (body: Y -> itree Es' Z): Any_tgt -> itree Es Any_tgt := fun varg_tgt =>
    varg_src <- trigger (Take Y);;
    x <- trigger (Take X);;
    rarg <- trigger (Take Σ);; forge rarg;; (*** virtual resource passing ***)
    (checkWf mn);;
    ord_cur <- trigger (Take _);;
    assume(P x varg_src varg_tgt rarg ord_cur);; (*** precondition ***)


    vret_src <- match ord_cur with
                | ord_pure n => (interp_hCallE_tgt mn ord_cur APC);; trigger (Choose _)
                | _ => (body_to_tgt mn ord_cur body) varg_src
                end;;
    (* vret_src <- body ord_cur varg_src;; (*** "rudiment": we don't remove extcalls because of termination-sensitivity ***) *)

    vret_tgt <- trigger (Choose Any_tgt);;
    '(mret, fret) <- trigger (Choose _);; put mn mret fret;; (*** updating resources in an abstract way ***)
    rret <- trigger (Choose Σ);; guarantee(Q x vret_src vret_tgt rret);; (*** postcondition ***)
    (discard rret);; (*** virtual resource passing ***)

    Ret vret_tgt (*** return ***)
  .

  Definition fun_to_tgt (fn: gname) (sb: fspecbody): (Any_tgt -> itree Es Any_tgt) :=
    let fs: fspec := sb.(fsb_fspec) in
    HoareFun fs.(mn) (fs.(precond)) (fs.(postcond)) sb.(fsb_body)
  .

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

  Variable sbtb: list (gname * fspecbody).
  Let stb: list (gname * fspec) := List.map (fun '(gn, fsb) => (gn, fsb_fspec fsb)) sbtb.
  Hypothesis WTY: ms_tgt.(ModSem.fnsems) = List.map (fun '(fn, sb) => (fn, fun_to_tgt stb fn sb)) sbtb.

  Definition ms_src: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, sb) => (fn, fun_to_src (fsb_body sb))) sbtb;
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

  Definition ms_mid: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, sb) => (fn, fun_to_mid (fsb_body sb))) sbtb;
    (* ModSem.initial_mrs := []; *)
    ModSem.initial_mrs := List.map (fun '(mn, (mr, mp)) => (mn, (ε, mp))) ms_tgt.(ModSem.initial_mrs);
    (*** Note: we don't use resources, so making everything as a unit ***)
  |}
  .

  Definition md_mid: Mod.t := {|
    Mod.get_modsem := fun _ => ms_mid;
    Mod.sk := Sk.unit;
    (*** It is already a whole-program, so we don't need Sk.t anymore. ***)
    (*** Note: Actually, md_tgt's sk could also have been unit, which looks a bit more uniform. ***)
  |}
  .













  Lemma interp_hCallE_src_bind
        `{E -< Es} A B
        (itr: itree (hCallE +' E) A) (ktr: A -> itree (hCallE +' E) B)
    :
      interp_hCallE_src (v <- itr ;; ktr v) = v <- interp_hCallE_src (itr);; interp_hCallE_src (ktr v)
  .
  Proof. unfold interp_hCallE_src. ired. grind. Qed.

  Lemma interp_hCallE_tgt_bind
        `{E -< Es} A B
        (itr: itree (hCallE +' E) A) (ktr: A -> itree (hCallE +' E) B)
        stb0 fn cur
    :
      interp_hCallE_tgt stb0 fn cur (v <- itr ;; ktr v) = v <- interp_hCallE_tgt stb0 fn cur (itr);; interp_hCallE_tgt stb0 fn cur (ktr v)
  .
  Proof. unfold interp_hCallE_tgt. ired. grind. Qed.

End CANCEL.

End PSEUDOTYPING.

















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

  Global Opaque Ordinal.from_nat.
  Global Opaque interp_Es.

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
