Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
From Ordinal Require Export Ordinal Arithmetic Inaccessible.
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



Arguments transl_all {Σ} _%string_scope {T}%type_scope _%itree_scope. (*** TODO: move to ModSem ***)

Notation "f ∘ g" := (fun x => (f (g x))). (*** TODO: move to Coqlib ***)

Inductive ord: Type :=
| ord_pure (n: Ord.t)
| ord_top
.

Definition is_pure (o: ord): bool := match o with | ord_pure _ => true | _ => false end.

Definition ord_lt (next cur: ord): Prop :=
  match next, cur with
  | ord_pure next, ord_pure cur => (next < cur)%ord
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


Section FSPEC.
  Context `{Σ: GRA.t}.

  Section FSPECTYPE.
    Variable AA AR: Type.

  (*** spec table ***)
    Record ftspec: Type := mk_ftspec {
      X: Type; (*** a meta-variable ***)
      precond: X -> AA -> Any_tgt -> ord -> Σ -> Prop; (*** meta-variable -> new logical arg -> current logical arg -> resource arg -> Prop ***)
      postcond: X -> AR -> Any_tgt -> Σ -> Prop; (*** meta-variable -> new logical ret -> current logical ret -> resource ret -> Prop ***)
    }
    .

    Definition ftspec_weaker (fsp_src fsp_tgt: ftspec): Prop :=
      forall (x_src: fsp_src.(X)),
      exists (x_tgt: fsp_tgt.(X)),
        (<<PRE: fsp_src.(precond) x_src <4= fsp_tgt.(precond) x_tgt>>) /\
        (<<POST: fsp_tgt.(postcond) x_tgt <3= fsp_src.(postcond) x_src>>)
    .

    Global Program Instance ftspec_weaker_PreOrder: PreOrder ftspec_weaker.
    Next Obligation.
    Proof.
      ii. exists x_src. esplits; eauto.
    Qed.
    Next Obligation.
    Proof.
      ii. hexploit (H x_src). i. des.
      hexploit (H0 x_tgt). i. des. esplits; eauto.
    Qed.
  End FSPECTYPE.

  (*** spec table ***)
  Record fspec: Type := mk_fspec {
    AA: Type;
    AR: Type;
    tspec:> ftspec AA AR;
  }
  .
  Coercion mk_fspec: ftspec >-> fspec.

  Variant fspec_weaker (fsp_src fsp_tgt: fspec): Prop :=
  | fspec_weaker_intro
      AA AR ftsp_src ftsp_tgt
      (FSPEC0: fsp_src = @mk_fspec AA AR ftsp_src)
      (FSPEC1: fsp_tgt = @mk_fspec AA AR ftsp_tgt)
      (WEAK: ftspec_weaker ftsp_src ftsp_tgt)
  .

  Global Program Instance fspec_weaker_PreOrder: PreOrder fspec_weaker.
  Next Obligation.
  Proof.
    ii. destruct x. econs; eauto. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H; inv H0. dependent destruction FSPEC0.
    econs; eauto. etrans; eauto.
  Qed.

  Definition mk (X AA AR: Type) (precond: X -> AA -> Any_tgt -> ord -> Σ -> Prop) (postcond: X -> AR -> Any_tgt -> Σ -> Prop) :=
    mk_ftspec precond postcond.
End FSPEC.


Section PROOF.
  (* Context {myRA} `{@GRA.inG myRA Σ}. *)
  Context {Σ: GRA.t}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.

  Definition HoareCall
             (tbr: bool)
             (ord_cur: ord)
             (fsp: fspec):
    gname -> fsp.(AA) -> itree Es fsp.(AR) :=
    fun fn varg_src =>
      '(marg, farg) <- trigger (Choose _);; put marg farg;; (*** updating resources in an abstract way ***)
      rarg <- trigger (Choose Σ);; discard rarg;; (*** virtual resource passing ***)
      x <- trigger (Choose fsp.(X));; varg_tgt <- trigger (Choose Any_tgt);;
      ord_next <- trigger (Choose _);;
      guarantee(fsp.(precond) x varg_src varg_tgt  ord_next rarg);; (*** precondition ***)

      guarantee(ord_lt ord_next ord_cur /\ (tbr = true -> is_pure ord_next) /\ (tbr = false -> ord_next = ord_top));;
      vret_tgt <- trigger (Call fn varg_tgt);; (*** call ***)

      rret <- trigger (Take Σ);; forge rret;; (*** virtual resource passing ***)
      vret_src <- trigger (Take fsp.(AR));;
      checkWf;;
      assume(fsp.(postcond) x vret_src vret_tgt rret);; (*** postcondition ***)

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

Program Fixpoint _APC (at_most: Ord.t) {wf Ord.lt at_most}: itree Es' unit :=
  break <- trigger (Choose _);;
  if break: bool
  then Ret tt
  else
    n <- trigger (Choose Ord.t);;
    trigger (Choose (n < at_most)%ord);;
    '(fn, varg) <- trigger (Choose _);;
    trigger (hCall true fn varg);;
    _APC n.
Next Obligation.
  eapply Ord.lt_well_founded.
Qed.

Definition APC: itree Es' unit :=
  at_most <- trigger (Choose _);;
  guarantee(at_most < kappa)%ord;;
  _APC at_most
.

Lemma unfold_APC:
  forall at_most, _APC at_most =
                  break <- trigger (Choose _);;
                  if break: bool
                  then Ret tt
                  else
                    n <- trigger (Choose Ord.t);;
                    guarantee (n < at_most)%ord;;
                    '(fn, varg) <- trigger (Choose _);;
                    trigger (hCall true fn varg);;
                    _APC n.
Proof.
  i. unfold _APC. rewrite Fix_eq; eauto.
  { repeat f_equal. extensionality break. destruct break; ss.
    repeat f_equal. extensionality n.
    unfold guarantee. rewrite bind_bind.
    repeat f_equal. extensionality p.
    rewrite bind_ret_l. repeat f_equal. extensionality x. destruct x. auto. }
  { i. replace g with f; auto. extensionality o. eapply H. }
Qed.
Global Opaque _APC.





Section CANCEL.

  Context `{Σ: GRA.t}.


  Record fspecbody: Type := mk_specbody {
    fsb_fspec:> fspec;
    fsb_body: fsb_fspec.(AA) -> itree (hCallE +' pE +' eventE) fsb_fspec.(AR);
  }
  .

  (*** argument remains the same ***)
  (* Definition mk_simple (mn: string) {X: Type} (P: X -> Any_tgt -> Σ -> ord -> Prop) (Q: X -> Any_tgt -> Σ -> Prop): fspec. *)
  (*   econs. *)
  (*   { apply mn. } *)
  (*   { i. apply (P X0 X2 X3 H /\ X1↑ = X2). } *)
  (*   { i. apply (Q X0 X2 X3 /\ X1↑ = X2). } *)
  (* Unshelve. *)
  (*   apply (list val). *)
  (*   apply (val). *)
  (* Defined. *)
  Definition mk_simple {X: Type} (PQ: X -> ((Any_tgt -> ord -> Σ -> Prop) * (Any_tgt -> Σ -> Prop))): ftspec (list val) (val) :=
    @mk_ftspec _ _ _ X (fun x y a o r => (fst ∘ PQ) x a o r /\ y↑ = a) (fun x z a r => (snd ∘ PQ) x a r /\ z↑ = a)
  .




  Section INTERP.
  (* Variable stb: gname -> option fspec. *)
  (*** TODO: I wanted to use above definiton, but doing so makes defining ms_src hard ***)
  (*** We can fix this by making ModSemL.fnsems to a function, but doing so will change the type of
       ModSemL.add to predicate (t -> t -> t -> Prop), not function.
       - Maybe not. I thought one needed to check uniqueness of gname at the "add",
         but that might not be the case.
         We may define fnsems: string -> option (list val -> itree Es val).
         When adding two ms, it is pointwise addition, and addition of (option A) will yield None when both are Some.
 ***)
  (*** TODO: try above idea; if it fails, document it; and refactor below with alist ***)
  Variable stb: list (gname * fspec).

  Definition handle_hCallE_src: hCallE ~> itree Es :=
    fun _ '(hCall tbr fn varg_src) =>
      match tbr with
      | true => tau;; trigger (Choose _)
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
    (cfun (body_to_src body))
  .





  Definition handle_hCallE_mid (ord_cur: ord): hCallE ~> itree Es :=
    fun _ '(hCall tbr fn varg_src) =>
      tau;;
      ord_next <- (if tbr then o0 <- trigger (Choose _);; Ret (ord_pure o0) else Ret ord_top);;
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
      vret_src <- (match ord_cur with
                   | ord_pure n => (interp_hCallE_mid ord_cur APC);; trigger (Choose _)
                   | _ => (body_to_mid ord_cur body) varg_src
                   end);;
      Ret vret_src↑
  .





  Definition handle_hCallE_tgt (ord_cur: ord): hCallE ~> itree Es :=
    fun _ '(hCall tbr fn varg_src) =>
      '(_, f) <- (List.find (fun '(_fn, _) => dec fn _fn) stb)ǃ;;
      varg_src <- varg_src↓ǃ;;
      vret_src <- (HoareCall tbr ord_cur f fn varg_src);;
      Ret vret_src↑
  .

  Definition interp_hCallE_tgt `{E -< Es} (ord_cur: ord): itree (hCallE +' E) ~> itree Es :=
    interp (case_ (bif:=sum1) (handle_hCallE_tgt ord_cur)
                  ((fun T X => trigger X): E ~> itree Es))
  .

  Definition body_to_tgt {AA AR} (ord_cur: ord)
             (body: AA -> itree (hCallE +' pE +' eventE) AR): AA -> itree Es AR :=
    fun varg_tgt => interp_hCallE_tgt ord_cur (body varg_tgt)
  .

  Definition HoareFun
             {X Y Z: Type}
             (P: X -> Y -> Any_tgt -> ord -> Σ -> Prop)
             (Q: X -> Z -> Any_tgt -> Σ -> Prop)
             (body: Y -> itree Es' Z): Any_tgt -> itree Es Any_tgt := fun varg_tgt =>
    varg_src <- trigger (Take Y);;
    x <- trigger (Take X);;
    rarg <- trigger (Take Σ);; forge rarg;; (*** virtual resource passing ***)
    (checkWf);;
    ord_cur <- trigger (Take _);;
    assume(P x varg_src varg_tgt  ord_cur rarg);; (*** precondition ***)


    vret_src <- match ord_cur with
                | ord_pure n => (interp_hCallE_tgt ord_cur APC);; trigger (Choose _)
                | _ => (body_to_tgt ord_cur body) varg_src
                end;;
    (* vret_src <- body ord_cur varg_src;; (*** "rudiment": we don't remove extcalls because of termination-sensitivity ***) *)

    vret_tgt <- trigger (Choose Any_tgt);;
    '(mret, fret) <- trigger (Choose _);; put mret fret;; (*** updating resources in an abstract way ***)
    rret <- trigger (Choose Σ);; guarantee(Q x vret_src vret_tgt rret);; (*** postcondition ***)
    (discard rret);; (*** virtual resource passing ***)

    Ret vret_tgt (*** return ***)
  .

  Definition fun_to_tgt (sb: fspecbody): (Any_tgt -> itree Es Any_tgt) :=
    let fs: fspec := sb.(fsb_fspec) in
    (HoareFun (fs.(precond)) (fs.(postcond)) sb.(fsb_body))
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



  Variable md_tgt: ModL.t.
  Let ms_tgt: ModSemL.t := (ModL.get_modsem md_tgt (Sk.load_skenv md_tgt.(ModL.sk))).

  Variable sbtb: list (gname * fspecbody).
  Let stb: list (gname * fspec) := List.map (fun '(gn, fsb) => (gn, fsb_fspec fsb)) sbtb.














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
        stb0 cur
    :
      interp_hCallE_tgt stb0 cur (v <- itr ;; ktr v) = v <- interp_hCallE_tgt stb0 cur (itr);; interp_hCallE_tgt stb0 cur (ktr v)
  .
  Proof. unfold interp_hCallE_tgt. ired. grind. Qed.

End CANCEL.

End PSEUDOTYPING.







Module SModSem.
Section SMODSEM.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    fnsems: list (gname * fspecbody);
    mn: mname;
    initial_mr: Σ;
    initial_st: Any.t;
  }
  .

  Definition transl (tr: fspecbody -> (Any.t -> itree Es Any.t)) (mr: t -> Σ) (ms: t): ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, sb) => (fn, tr sb)) ms.(fnsems);
    ModSem.mn := ms.(mn);
    ModSem.initial_mr := mr ms;
    ModSem.initial_st := ms.(initial_st);
  |}
  .

  Definition to_src (ms: t): ModSem.t := transl (fun_to_src ∘ fsb_body) (fun _ => ε) ms.
  Definition to_mid (ms: t): ModSem.t := transl (fun_to_mid ∘ fsb_body) (fun _ => ε) ms.
  Definition to_tgt (stb: list (gname * fspec)) (ms: t): ModSem.t := transl (fun_to_tgt stb) (initial_mr) ms.

  Definition main (mainpre: Any.t -> ord -> Σ -> Prop) (mainbody: list val -> itree (hCallE +' pE +' eventE) val): t := {|
      fnsems := [("main", (mk_specbody (mk_simple (fun (_: unit) => (mainpre, top2))) mainbody))];
      mn := "Main";
      initial_mr := ε;
      initial_st := tt↑;
    |}
  .

End SMODSEM.
End SModSem.



Module SMod.
Section SMOD.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    get_modsem: SkEnv.t -> SModSem.t;
    sk: Sk.t;
  }
  .

  Definition transl (tr: SkEnv.t -> fspecbody -> (Any.t -> itree Es Any.t)) (mr: SModSem.t -> Σ) (md: t): Mod.t := {|
    Mod.get_modsem := fun skenv => SModSem.transl (tr skenv) mr (md.(get_modsem) skenv);
    Mod.sk := md.(sk);
  |}
  .

  Definition to_src (md: t): Mod.t := transl (fun _ => fun_to_src ∘ fsb_body) (fun _ => ε) md.
  Definition to_mid (md: t): Mod.t := transl (fun _ => fun_to_mid ∘ fsb_body) (fun _ => ε) md.
  Definition to_tgt (stb: SkEnv.t -> list (gname * fspec)) (md: t): Mod.t := transl (fun_to_tgt ∘ stb) SModSem.initial_mr md.

  (* Definition transl (tr: SModSem.t -> ModSem.t) (md: t): Mod.t := {| *)
  (*   Mod.get_modsem := (SModSem.transl tr) ∘ md.(get_modsem); *)
  (*   Mod.sk := md.(sk); *)
  (* |} *)
  (* . *)

  (* Definition to_src (md: t): Mod.t := transl SModSem.to_src md. *)
  (* Definition to_mid (md: t): Mod.t := transl SModSem.to_mid md. *)
  (* Definition to_tgt (stb: list (gname * fspec)) (md: t): Mod.t := transl (SModSem.to_tgt stb) md. *)
  Lemma to_src_comm: forall skenv smd,
      (SModSem.to_src) (get_modsem smd skenv) = (to_src smd).(Mod.get_modsem) skenv.
  Proof. refl. Qed.
  Lemma to_mid_comm: forall skenv smd,
      (SModSem.to_mid) (get_modsem smd skenv) = (to_mid smd).(Mod.get_modsem) skenv.
  Proof. refl. Qed.
  Lemma to_tgt_comm: forall skenv stb smd,
      (SModSem.to_tgt (stb skenv)) (get_modsem smd skenv) = (to_tgt stb smd).(Mod.get_modsem) skenv.
  Proof. refl. Qed.









  Notation "(∘)" := (fun f g => f ∘ g) (at level 59).

  (* Definition l_bind A B (x: list A) (f: A -> list B): list B := List.flat_map f x. *)
  (* Definition l_ret A (a: A): list A := [a]. *)

  Declare Scope l_monad_scope.
  Local Open Scope l_monad_scope.
  Notation "'do' X <- A ; B" := (List.flat_map (fun X => B) A) : l_monad_scope.
  Notation "'do' ' X <- A ; B" := (List.flat_map (fun _x => match _x with | X => B end) A) : l_monad_scope.
  Notation "'ret'" := (fun X => [X]) (at level 60) : l_monad_scope.

  Lemma unconcat
        A (xs: list A)
    :
      List.concat (List.map (fun x => [x]) xs) = xs
  .
  Proof.
    induction xs; ii; ss. f_equal; ss.
  Qed.

  Lemma red_do_ret A B (xs: list A) (f: A -> B)
    :
      (do x <- xs; ret (f x)) = List.map f xs
  .
  Proof.
    rewrite flat_map_concat_map.
    erewrite <- List.map_map with (f:=f) (g:=ret).
    rewrite unconcat. ss.
  Qed.











  Local Opaque Mod.add_list.

  Lemma transl_sk
        tr0 mr0 mds
    :
      <<SK: ModL.sk (Mod.add_list (List.map (transl tr0 mr0) mds)) = fold_right Sk.add Sk.unit (List.map sk mds)>>
  .
  Proof.
    induction mds; ii; ss.
    rewrite Mod.add_list_cons. ss. r. f_equal. ss.
  Qed.

  Lemma transl_sk_stable
        tr0 tr1 mr0 mr1 mds
    :
      ModL.sk (Mod.add_list (List.map (transl tr0 mr0) mds)) =
      ModL.sk (Mod.add_list (List.map (transl tr1 mr1) mds))
  .
  Proof. rewrite ! transl_sk. ss. Qed.

  Definition load_fnsems (skenv: SkEnv.t) (mds: list t) (tr0: fspecbody -> Any.t -> itree Es Any.t) :=
    do md <- mds;
    let ms := (get_modsem md skenv) in
      (do '(fn, fsb) <- ms.(SModSem.fnsems);
       let fsem := tr0 fsb in
       ret (fn, transl_all ms.(SModSem.mn) ∘ fsem))
  .

  Let transl_fnsems_aux
        tr0 mr0 mds
        (skenv: SkEnv.t)
    :
      (ModSemL.fnsems (ModL.get_modsem (Mod.add_list (List.map (transl tr0 mr0) mds)) skenv)) =
      (load_fnsems skenv mds (tr0 skenv))
  .
  Proof.
    induction mds; ii; ss.
    rewrite Mod.add_list_cons. cbn. f_equal; ss.
    rewrite ! List.map_map.

    rewrite flat_map_concat_map.
    replace (fun _x: string * fspecbody => let (fn, fsb) := _x in [(fn, transl_all (SModSem.mn (get_modsem a skenv)) ∘ (tr0 skenv fsb))]) with
        (ret ∘ (fun _x: string * fspecbody => let (fn, fsb) := _x in (fn, transl_all (SModSem.mn (get_modsem a skenv)) ∘ (tr0 skenv fsb))));
      cycle 1.
    { apply func_ext. i. des_ifs. }
    erewrite <- List.map_map with (g:=ret).
    rewrite unconcat.
    apply map_ext. ii. des_ifs.
  Qed.

  Lemma transl_fnsems
        tr0 mr0 mds
    :
      (ModSemL.fnsems (ModL.enclose (Mod.add_list (List.map (transl tr0 mr0) mds)))) =
      (load_fnsems (Sk.load_skenv (List.fold_right Sk.add Sk.unit (List.map sk mds))) mds (tr0 (Sk.load_skenv (List.fold_right Sk.add Sk.unit (List.map sk mds)))))
  .
  Proof.
    unfold ModL.enclose.
    rewrite transl_fnsems_aux. do 2 f_equal. rewrite transl_sk. ss.
    rewrite transl_sk. auto.
  Qed.

  Lemma flat_map_assoc
        A B C
        (f: A -> list B)
        (g: B -> list C)
        (xs: list A)
    :
      (do y <- (do x <- xs; f x); g y) =
      (do x <- xs; do y <- (f x); g y)
  .
  Proof.
    induction xs; ii; ss.
    rewrite ! flat_map_concat_map in *. rewrite ! map_app. rewrite ! concat_app. f_equal; ss.
  Qed.

  Lemma transl_fnsems_stable
        tr0 tr1 mr0 mr1 mds
    :
      List.map fst (ModL.enclose (Mod.add_list (List.map (transl tr0 mr0) mds))).(ModSemL.fnsems) =
      List.map fst (ModL.enclose (Mod.add_list (List.map (transl tr1 mr1) mds))).(ModSemL.fnsems)
  .
  Proof.
    rewrite ! transl_fnsems.
    unfold load_fnsems.
    rewrite <- ! red_do_ret.
    rewrite ! flat_map_assoc. eapply flat_map_ext. i.
    rewrite ! flat_map_assoc. eapply flat_map_ext. i.
    des_ifs.
  Qed.




  Definition load_initial_mrs (skenv: SkEnv.t) (mds: list t) (mr0: SModSem.t -> Σ): list (string * (Σ * Any.t)) :=
    do md <- mds;
    let ms := (get_modsem md skenv) in
    ret (ms.(SModSem.mn), (mr0 ms, ms.(SModSem.initial_st)))
  .

  Let transl_initial_mrs_aux
        tr0 mr0 mds
        (skenv: SkEnv.t)
    :
      (ModSemL.initial_mrs (ModL.get_modsem (Mod.add_list (List.map (transl tr0 mr0) mds)) skenv)) =
      (load_initial_mrs skenv mds mr0)
  .
  Proof.
    induction mds; ii; ss.
    rewrite Mod.add_list_cons. cbn. f_equal; ss.
  Qed.

  Lemma transl_initial_mrs
        tr0 mr0 mds
    :
      (ModSemL.initial_mrs (ModL.enclose (Mod.add_list (List.map (transl tr0 mr0) mds)))) =
      (load_initial_mrs (Sk.load_skenv (List.fold_right Sk.add Sk.unit (List.map sk mds))) mds mr0)
  .
  Proof.
    unfold ModL.enclose.
    rewrite transl_initial_mrs_aux. do 2 f_equal. rewrite transl_sk. ss.
  Qed.

  Lemma transl_stable_mn
        tr0 tr1 mr0 mr1 mds
    :
      List.map fst (ModL.enclose (Mod.add_list (List.map (transl tr0 mr0) mds))).(ModSemL.initial_mrs) =
      List.map fst (ModL.enclose (Mod.add_list (List.map (transl tr1 mr1) mds))).(ModSemL.initial_mrs)
  .
  Proof.
    rewrite ! transl_initial_mrs. unfold load_initial_mrs. rewrite <- ! red_do_ret.
    rewrite ! flat_map_assoc. eapply flat_map_ext. i. ss.
  Qed.

  Definition main (mainpre: Any.t -> ord -> Σ -> Prop) (mainbody: list val -> itree (hCallE +' pE +' eventE) val): t := {|
    get_modsem := fun _ => (SModSem.main mainpre mainbody);
    sk := Sk.unit;
  |}
  .

End SMOD.
End SMod.















  Hint Resolve Ord.lt_le_lt Ord.le_lt_lt OrdArith.lt_add_r OrdArith.le_add_l
       OrdArith.le_add_r Ord.lt_le
       Ord.lt_S
       Ord.S_lt
       Ord.S_supremum
       Ord.S_pos
    : ord.
  Hint Resolve Ord.le_trans Ord.lt_trans: ord_trans.
  Hint Resolve OrdArith.add_base_l OrdArith.add_base_r: ord_proj.

  Global Opaque EventsL.interp_Es.

  Require Import SimGlobal.






  Require Import Red.

  Ltac interp_red := rewrite interp_vis ||
                             rewrite interp_ret ||
                             rewrite interp_tau ||
                             rewrite interp_trigger ||
                             rewrite interp_bind.

  Ltac _red_itree f :=
    match goal with
    | [ |- ITree.bind' _ ?itr = _] =>
      match itr with
      | ITree.bind' _ _ =>
        instantiate (f:=_continue); apply bind_bind; fail
      | Tau _ =>
        instantiate (f:=_break); apply bind_tau; fail
      | Ret _ =>
        instantiate (f:=_continue); apply bind_ret_l; fail
      | _ =>
        fail
      end
    | _ => fail
    end.

  (*** TODO: Move to ModSem.v ***)
  Lemma interp_Es_unwrapU
        `{Σ: GRA.t}
        prog R st0 (r: option R)
    :
      EventsL.interp_Es prog (unwrapU r) st0 = r <- unwrapU r;; Ret (st0, r)
  .
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite EventsL.interp_Es_ret. grind.
    - rewrite EventsL.interp_Es_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma interp_Es_unwrapN
        `{Σ: GRA.t}
        prog R st0 (r: option R)
    :
      EventsL.interp_Es prog (unwrapN r) st0 = r <- unwrapN r;; Ret (st0, r)
  .
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite EventsL.interp_Es_ret. grind.
    - rewrite EventsL.interp_Es_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma interp_Es_assume
        `{Σ: GRA.t}
        prog st0 (P: Prop)
    :
      EventsL.interp_Es prog (assume P) st0 = assume P;; tau;; tau;; tau;; Ret (st0, tt)
  .
  Proof.
    unfold assume.
    repeat (try rewrite EventsL.interp_Es_bind; try rewrite bind_bind). grind.
    rewrite EventsL.interp_Es_eventE.
    repeat (try rewrite EventsL.interp_Es_bind; try rewrite bind_bind). grind.
    rewrite EventsL.interp_Es_ret.
    refl.
  Qed.

  Lemma interp_Es_guarantee
        `{Σ: GRA.t}
        prog st0 (P: Prop)
    :
      EventsL.interp_Es prog (guarantee P) st0 = guarantee P;; tau;; tau;; tau;; Ret (st0, tt)
  .
  Proof.
    unfold guarantee.
    repeat (try rewrite EventsL.interp_Es_bind; try rewrite bind_bind). grind.
    rewrite EventsL.interp_Es_eventE.
    repeat (try rewrite EventsL.interp_Es_bind; try rewrite bind_bind). grind.
    rewrite EventsL.interp_Es_ret.
    refl.
  Qed.





Ltac _red_Es_aux f itr :=
  match itr with
  | ITree.bind' _ _ =>
    instantiate (f:=_continue); eapply EventsL.interp_Es_bind; fail
  | Tau _ =>
    instantiate (f:=_break); apply EventsL.interp_Es_tau; fail
  | Ret _ =>
    instantiate (f:=_continue); apply EventsL.interp_Es_ret; fail
  | trigger ?e =>
    instantiate (f:=_break);
    match (type of e) with
    | context[callE] => apply EventsL.interp_Es_callE
    | context[eventE] => apply EventsL.interp_Es_eventE
    | context[EventsL.pE] => apply EventsL.interp_Es_pE
    | context[EventsL.rE] => apply EventsL.interp_Es_rE
    | _ => fail 2
    end
  | triggerUB =>
    instantiate (f:=_break); apply EventsL.interp_Es_triggerUB; fail
  | triggerNB =>
    instantiate (f:=_break); apply EventsL.interp_Es_triggerNB; fail
  | unwrapU _ =>
    instantiate (f:=_break); apply interp_Es_unwrapU; fail
  | unwrapN _ =>
    instantiate (f:=_break); apply interp_Es_unwrapN; fail
  | assume _ =>
    instantiate (f:=_break); apply interp_Es_assume; fail
  | guarantee _ =>
    instantiate (f:=_break); apply interp_Es_guarantee; fail
  | _ =>
    fail
  end
.

(*** TODO: move to ITreeLib ***)
Lemma bind_eta E X Y itr0 itr1 (ktr: ktree E X Y): itr0 = itr1 -> itr0 >>= ktr = itr1 >>= ktr. i; subst; refl. Qed.

Ltac _red_Es f :=
  match goal with
  | [ |- ITree.bind' _ (EventsL.interp_Es _ ?itr _) = _ ] =>
    eapply bind_eta; _red_Es_aux f itr
  | [ |- EventsL.interp_Es _ ?itr _ = _] =>
    _red_Es_aux f itr
  | _ => fail
  end.

Ltac _red_lsim f :=
  (_red_Es f) || (_red_itree f) || (fail).

Ltac ired_l := try (prw _red_lsim 2 0).
Ltac ired_r := try (prw _red_lsim 1 0).

Ltac ired_both := ired_l; ired_r.

  Ltac mred := repeat (cbn; ired_both).
  Ltac Esred :=
            try rewrite ! EventsL.interp_Es_rE; try rewrite ! EventsL.interp_Es_pE;
            try rewrite ! EventsL.interp_Es_eventE; try rewrite ! EventsL.interp_Es_callE;
            try rewrite ! EventsL.interp_Es_triggerNB; try rewrite ! EventsL.interp_Es_triggerUB (*** igo ***).
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
      (gstep; econs; eauto; try (by eapply OrdArith.lt_from_nat; ss);
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

  From ExtLib Require Import
       Data.Map.FMapAList.

  Hint Resolve cpn3_wcompat: paco.
  Ltac init :=
    split; ss; ii; clarify; rename y into varg; eexists 100%nat; ss; des; clarify;
    ginit; []; unfold alist_add, alist_remove; ss;
    unfold fun_to_tgt, cfun, HoareFun; ss.
