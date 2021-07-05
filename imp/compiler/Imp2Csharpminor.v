Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.

Require Import Coq.Lists.SetoidList.

From compcert Require Import
     Ctypes AST Integers Cminor Csharpminor Globalenvs Linking Errors Cminorgen Behaviors Events.

From compcert Require Compiler.

Import Int.

Set Implicit Arguments.

Parameter s2p: string -> ident.
Parameter s2p_inj: forall x y, (s2p x) = (s2p y) -> x = y.

Class builtinsTy: Type := mk { bts0:> list (string * (external_function)) }.

Section Compile.

  (* compile each program indiv,
     prove behavior refinement for whole (closed) prog after linking *)
  Let tgt_gdef := globdef fundef ().
  Let tgt_gdefs := list (ident * tgt_gdef).

  (* Definition ident_key {T} (id: ident) l : option T := alist_find id l. *)

  Fixpoint compile_expr (expr: Imp.expr) : Csharpminor.expr :=
    match expr with
    | Var x => Evar (s2p x)
    | Lit z => Econst (Olongconst (Int64.repr z))
    | Eq a b =>
      let ca := compile_expr a in let cb := compile_expr b in Eunop Olongofint (Ebinop (Ocmpl Ceq) ca cb)
    | Lt a b =>
      let ca := compile_expr a in let cb := compile_expr b in Eunop Olongofint (Ebinop (Ocmpl Clt) ca cb)
    | Plus a b =>
      let ca := compile_expr a in let cb := compile_expr b in (Ebinop Oaddl ca cb)
    | Minus a b =>
      let ca := compile_expr a in let cb := compile_expr b in (Ebinop Osubl ca cb)
    | Mult a b =>
      let ca := compile_expr a in let cb := compile_expr b in (Ebinop Omull ca cb)
    end
  .

  Definition compile_exprs (exprs: list Imp.expr) : list Csharpminor.expr := List.map (compile_expr) exprs.

  Definition make_signature n := mksignature (repeat Tlong n) (Tlong) (cc_default).

  (* Imp has no type, value is either int64/ptr64 -> sem_cast can convert *)
  Fixpoint compile_stmt (stmt: Imp.stmt) : Csharpminor.stmt :=
    match stmt with
    | Skip =>
      Sskip
    | Assign x e =>
      let ex := compile_expr e in (Sset (s2p x) ex)
    | Seq s1 s2 =>
      let cs1 := (compile_stmt s1) in
      let cs2 := (compile_stmt s2) in
      (Sseq cs1 cs2)
    | If cond sif selse =>
      let cc := (compile_expr cond) in
      let cif := (compile_stmt sif) in
      let celse := (compile_stmt selse) in
      let bexp := Ebinop (Ocmpl Cne) cc (Econst (Olongconst Int64.zero)) in
      (Sifthenelse bexp cif celse)

    | CallFun x f args =>
      let id := s2p f in
      let sig := (make_signature (List.length args)) in
      let al := (compile_exprs args) in
      (Scall (Some (s2p x)) sig (Eaddrof id) al)

    (* only supports call by ptr with a variable (no other expr) (syntatic check would be nice here...) *)
    | CallPtr x pe args =>
      match pe with
      | Var y =>
        let sig := make_signature (length args) in
        let al := (compile_exprs args) in
        (Scall (Some (s2p x)) sig (Evar (s2p y)) al)
      | _ => Sskip
      end

    | CallSys x f args =>
      let id := s2p f in
      let sig := (make_signature (List.length args)) in
      let al := (compile_exprs args) in
      (Scall (Some (s2p x)) sig (Eaddrof id) al)

    | AddrOf x gn =>
      let id := s2p gn in
      (Sset (s2p x) (Eaddrof id))

    | Malloc x se =>
      let a := (compile_expr se) in
      let adjofs := Ebinop Omull (Econst (Olongconst (Int64.repr 8))) a in
      (Scall (Some (s2p x)) (ef_sig EF_malloc) (Eaddrof (s2p "malloc")) [adjofs])
    | Free pe =>
      let p := (compile_expr pe) in
      (Sseq Sskip Sskip)
    | Load x pe =>
      let cpe := (compile_expr pe) in
      (Sset (s2p x) (Eload Mint64 cpe))
    | Store pe ve =>
      let cpe := (compile_expr pe) in
      let cve := (compile_expr ve) in
      (Sstore Mint64 cpe cve)
    | Cmp x ae be =>
      let cae := (compile_expr ae) in
      let cbe := (compile_expr be) in
      let cmpexpr := Eunop Olongofint (Ebinop (Ocmplu Ceq) cae cbe) in
      (Sset (s2p x) cmpexpr)
    end
  .

  (** memory accessing calls *)
  (** load, store, cmp are translated to non-function calls. *)
  (** register alloc and free in advance so can be properly called *)
  Let malloc_def : fundef := External EF_malloc.
  Let free_def : fundef := External EF_free.

  Definition compile_eVar : string -> (ident * tgt_gdef) :=
    fun id => (s2p id, Gvar (mkglobvar () [] false false)).

  Definition compile_eVars (src : extVars) : tgt_gdefs := List.map compile_eVar src.


  Definition compile_iVar : (string * Z) -> (ident * tgt_gdef) :=
    fun '(id, z) => (s2p id, Gvar (mkglobvar () [Init_int64 (Int64.repr z)] false false)).

  Definition compile_iVars (src : progVars) : tgt_gdefs := List.map compile_iVar src.


  Definition compile_eFun : (string * nat) -> (ident * tgt_gdef) :=
    fun '(id, a) => (s2p id, Gfun (External (EF_external id (make_signature a)))).

  Definition compile_eFuns (src : extFuns) : tgt_gdefs := List.map compile_eFun src.


  Definition compile_iFun : (string * (string * Imp.function)) -> (ident * tgt_gdef) :=
    fun '(_, (fn, f)) =>
      let params := (List.map (fun vn => s2p vn) f.(Imp.fn_params)) in
      let temps := (List.map (fun vn => s2p vn) f.(Imp.fn_vars)) ++ [(s2p "return"); (s2p "_")] in
      let sig := if (rel_dec fn "main"%string) then signature_main else (make_signature (List.length params)) in
      let _body := compile_stmt f.(Imp.fn_body) in
      let body :=
          if (rel_dec fn "main"%string)
          then (Sseq _body (Sreturn (Some (Eunop Ointoflong (Evar (s2p "return"))))))
          else (Sseq _body (Sreturn (Some (Evar (s2p "return"))))) in
      let fdef := {|
            fn_sig := sig;
            fn_params := params;
            fn_vars := [];
            fn_temps := temps;
            fn_body := body;
          |} in
      (s2p fn, Gfun (Internal fdef)).

  Definition compile_iFuns (src : list (string * (string * Imp.function))) : tgt_gdefs := List.map compile_iFun src.


  Context `{builtins : builtinsTy}.

  Definition bts : list (string * tgt_gdef) :=
    List.map (fun '(name, ef) => (name, Gfun (External ef))) bts0.
  Definition init_g0 : list (string * tgt_gdef) :=
    bts ++ [("malloc"%string, Gfun malloc_def); ("free"%string, Gfun free_def)].

  Definition init_g : tgt_gdefs := List.map (fun '(name, fd) => (s2p name, fd)) init_g0.


  Definition c_sys := List.map compile_eFun syscalls.

  Definition compile_gdefs (src : Imp.programL) : tgt_gdefs :=
    let evars := compile_eVars src.(ext_varsL) in
    let ivars := compile_iVars src.(prog_varsL) in
    let efuns := compile_eFuns src.(ext_funsL) in
    let ifuns := compile_iFuns src.(prog_funsL) in
    let defs := init_g ++ c_sys ++ efuns ++ evars ++ ifuns ++ ivars in
    defs.

  Definition compile (src : Imp.programL) : res program :=
    let _defs := (compile_gdefs src) in
    if (Coqlib.list_norepet_dec dec (List.map fst _defs)) then
      let pdefs := Maps.PTree_Properties.of_list _defs in
      let defs := Maps.PTree.elements pdefs in
      let pubs := (List.map (s2p ∘ fst) init_g0) ++ (List.map s2p src.(publicL)) in
      OK (mkprogram defs pubs (s2p "main"))
    else Error [MSG "Imp2csharpminor compilation failed; duplicated declarations"]
  .

  Definition compile_imp p := compile (lift p).

End Compile.

Global Opaque init_g0.
Global Opaque init_g.





Lemma option2bool {T} :
  forall x : option T,
    {match x with | Some _ => True | None => False end} +
    {~ match x with | Some _ => True | None => False end}.
Proof.
  i. destruct x.
  - left. auto.
  - right. auto.
Qed.

Definition extFun_Dec : forall x y : (string * nat), {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Qed.

Section LINK.

  Import Permutation.

  Context `{builtins : builtinsTy}.

  Definition name1 {A} {B} (l: list (A * B)) := List.map fst l.
  Definition name2 {A} {B} {C} (l: list (A * (B * C))) := List.map (fst ∘ snd) l.

  Variable src1 : Imp.programL.
  Variable src2 : Imp.programL.

  Definition l_nameL := src1.(nameL) ++ src2.(nameL).
  Definition l_pvs := src1.(prog_varsL) ++ src2.(prog_varsL).
  Definition l_pfs := src1.(prog_funsL) ++ src2.(prog_funsL).
  Definition l_publicL := src1.(publicL) ++ (List.map fst init_g0) ++ src2.(publicL).
  Definition l_defsL := src1.(defsL) ++ src2.(defsL).

  (* (if/if) (if/iv) (if/ef) (if/ev) |
     (iv/if) (iv/iv) (iv/ef) (iv/ev) |
     (ef/if) (ef/iv) (ef/ef) (ef/ev) |
     (ev/if) (ev/iv) (ev/ef) 16.(ev/ev) 
  *)

  (* check external decls are consistent *)
  (* 13.ev/if, 4.if/ev, 10.ef/iv, 7.iv/ef, 15.ev/ef, 12.ef/ev *)
  Definition link_imp_cond1 :=
    let sd := string_Dec in
    let c1 := Coqlib.list_norepet_dec dec (src1.(ext_varsL) ++ (name2 l_pfs)) in
    let c2 := Coqlib.list_norepet_dec dec (src2.(ext_varsL) ++ (name2 l_pfs)) in
    let c3 := Coqlib.list_norepet_dec dec ((name1 src1.(ext_funsL)) ++ (name1 l_pvs)) in
    let c4 := Coqlib.list_norepet_dec dec ((name1 src2.(ext_funsL)) ++ (name1 l_pvs)) in
    let c5 := Coqlib.list_norepet_dec dec (src1.(ext_varsL) ++ (name1 src2.(ext_funsL))) in
    let c6 := Coqlib.list_norepet_dec dec (src2.(ext_varsL) ++ (name1 src1.(ext_funsL))) in
    c1 && c2 && c3 && c4 && c5 && c6.

  Lemma link_imp_cond1_prop :
    forall (_LIC2: link_imp_cond1 = true),
      (<<EV1: Coqlib.list_norepet (src1.(ext_varsL) ++ (name2 l_pfs))>>) /\
      (<<EV2: Coqlib.list_norepet (src2.(ext_varsL) ++ (name2 l_pfs))>>) /\
      (<<EF1: Coqlib.list_norepet ((name1 src1.(ext_funsL)) ++ (name1 l_pvs))>>) /\
      (<<EF1: Coqlib.list_norepet ((name1 src2.(ext_funsL)) ++ (name1 l_pvs))>>) /\
      (<<EVF1: Coqlib.list_norepet (src1.(ext_varsL) ++ (name1 src2.(ext_funsL)))>>) /\
      (<<EVF2: Coqlib.list_norepet (src2.(ext_varsL) ++ (name1 src1.(ext_funsL)))>>).
  Proof.
    i. unfold link_imp_cond1 in _LIC2. bsimpl. des.
    apply sumbool_to_bool_true in _LIC2. apply sumbool_to_bool_true in _LIC3.
    apply sumbool_to_bool_true in _LIC1. apply sumbool_to_bool_true in _LIC0.
    apply sumbool_to_bool_true in _LIC5. apply sumbool_to_bool_true in _LIC4.
    repeat split; eauto.
  Qed.

  (* check external fun decls' sig *)
  Fixpoint _link_imp_cond2' (p : string * nat) (l : extFuns) :=
    let '(id, n) := p in
    match l with
    | [] => true
    | (id2, n2) :: t =>
      if (eqb id id2 && negb (n =? n2)%nat) then false
      else _link_imp_cond2' p t
    end
  .

  Lemma _link_imp_cond2'_prop :
    forall p (l : list (string * nat))
      (_LIC2': _link_imp_cond2' p l = true),
      <<_LIC2: forall a, ((In a l) /\ (fst a = fst p)) -> (snd a = snd p)>>.
  Proof.
    i. red. depgen p. depgen l. clear. induction l; ii; ss; clarify.
    { des. clarify. }
    des; clarify; ss.
    { destruct p; ss. destruct a0; ss. clarify. des_ifs. bsimpl. des; bsimpl; ss; clarify.
      { rewrite eqb_refl in Heq. clarify. }
      rewrite Nat.eqb_eq in Heq. ss. }
    destruct p. destruct a0. ss; clarify. destruct a. ss; clarify. des_ifs. bsimpl. des.
    { set (k0:=(s, n0)) in *. set (k:=(s, n)) in *. eapply IHl in _LIC2'.
      { instantiate (1:=k0) in _LIC2'. subst k; subst k0; ss; clarify. }
      split; auto. }
    rewrite Nat.eqb_eq in Heq. clarify. eapply IHl in _LIC2'.
    { instantiate (1:= (s, n0)) in _LIC2'. ss; clarify. }
    split; ss; eauto.
  Qed.

  Lemma _link_imp_cond2'_prop_perm :
    forall p (l1 l2 : list (string * nat))
      (PERM: Permutation l1 l2)
      (_LIC2': _link_imp_cond2' p l1 = true),
      <<_LIC2: _link_imp_cond2' p l2 = true>>.
  Proof.
    i. red. depgen PERM. depgen _LIC2'. clear. i. depgen p. induction PERM; i; ss; clarify.
    - destruct p; ss; clarify. destruct x; ss; clarify. des_ifs. eauto.
    - destruct p; ss; clarify. destruct x; ss; clarify. destruct y; ss; clarify. des_ifs.
    - eauto.
  Qed.

  Fixpoint _link_imp_cond2 l :=
    match l with
    | [] => true
    | h :: t =>
      if (_link_imp_cond2' h t) then _link_imp_cond2 t
      else false
    end
  .

  Lemma _link_imp_cond2_prop :
    forall (l : list (string * nat))
      (_LIC3: _link_imp_cond2 l = true),
      <<_LIC3: forall a b, ((In a l) /\ (In b l) /\ (fst a = fst b)) -> (snd a = snd b)>>.
  Proof.
    i. red. depgen l. clear. induction l; i; ss; clarify.
    { des; clarify. }
    des; ss; clarify.
    - des_ifs. eapply _link_imp_cond2'_prop in Heq. eapply Heq; eauto.
    - des_ifs. eapply _link_imp_cond2'_prop in Heq. sym; eapply Heq; eauto.
    - des_ifs. assert (TRUE: true = true); auto.
  Qed.

  Lemma _link_imp_cond2_prop_perm :
    forall (l1 l2 : list (string * nat))
      (PERM: Permutation l1 l2)
      (_LIC3: _link_imp_cond2 l1 = true),
      <<_LIC3: _link_imp_cond2 l2 = true>>.
  Proof.
    i. red. clear src1 src2. depgen _LIC3. induction PERM; i; ss; clarify.
    - des_ifs.
      + eauto.
      + hexploit _link_imp_cond2'_prop_perm; eauto.
    - destruct x; destruct y; ss; clarify. des_ifs. bsimpl. des.
      + rewrite eqb_eq in Heq0. rewrite eqb_neq in Heq3. clarify.
      + rewrite Nat.eqb_eq in Heq3. rewrite Nat.eqb_neq in Heq4. clarify.
    - eauto.
  Qed.

  (* 11.ef/ef *)
  Definition link_imp_cond2 := _link_imp_cond2 (src1.(ext_funsL) ++ src2.(ext_funsL)).

  Lemma link_imp_cond2_prop :
    forall (LIC3: link_imp_cond2 = true),
      <<LIC3P: forall a b, ((In a (src1.(ext_funsL) ++ src2.(ext_funsL))) /\ (In b (src1.(ext_funsL) ++ src2.(ext_funsL)))
                       /\ (fst a = fst b)) -> (snd a = snd b)>>.
  Proof.
    i. unfold link_imp_cond2 in LIC3. eapply _link_imp_cond2_prop in LIC3. auto.
  Qed.

  (* merge external decls; vars is simple, funs assumes cond2 is passed *)
  (* link external decls; need to remove defined names *)

  (* 8.iv/ev, 14.ev/iv *)
  Definition l_evs :=
    let l_evs0 := nodup string_Dec (src1.(ext_varsL) ++ src2.(ext_varsL)) in
    let l_pvsn := name1 l_pvs in
    List.filter (fun s => negb (in_dec string_Dec s l_pvsn)) l_evs0.

  (* 3.if/ef, 9.ef/if *)
  Definition l_efs :=
    let l_efs0 := nodup extFun_Dec (src1.(ext_funsL) ++ src2.(ext_funsL)) in
    let l_pfsn := name2 l_pfs in
    List.filter (fun sn => negb (in_dec string_Dec (fst sn) l_pfsn)) l_efs0.


  (* check names are unique *)
  Definition link_imp_cond3 :=
    Coqlib.list_norepet_dec dec ((name1 init_g0) ++ (name1 syscalls) ++
                                 (name1 l_efs) ++ (l_evs) ++ (name2 l_pfs) ++ (name1 l_pvs)).

  Lemma link_imp_cond3_prop :
    forall (_LIC3: link_imp_cond3),
    <<LIC3: Coqlib.list_norepet ((name1 init_g0) ++ (name1 syscalls) ++
                                 (name1 l_efs) ++ (l_evs) ++ (name2 l_pfs) ++ (name1 l_pvs))>>.
  Proof.
    i. unfold link_imp_cond3 in *. apply sumbool_to_bool_true in _LIC3. ss.
  Qed.

  Lemma _link_imp_cond3_ints :
    forall (_LIC3: link_imp_cond3),
      <<INTS: Coqlib.list_norepet ((name2 (prog_funsL src1)) ++ (name2 (prog_funsL src2)) ++
                                   (name1 (prog_varsL src1)) ++ (name1 (prog_varsL src2)))>>.
  Proof.
    ii. red. apply link_imp_cond3_prop in _LIC3. des.
    do 4 (apply Coqlib.list_norepet_append_right in _LIC3).
    unfold l_pfs in _LIC3; unfold l_pvs in _LIC3. unfold name2 in *; unfold name1 in *.
    rewrite ! map_app in _LIC3. rewrite <- app_assoc in _LIC3. auto.
  Qed.

  (* 1.if/if, 2.if/iv, 5.iv/if, 6.iv/iv *)
  Lemma link_imp_cond3_ints :
    forall (_LIC3: link_imp_cond3),
      (<<IFIF: Coqlib.list_disjoint (name2 (prog_funsL src1)) (name2 (prog_funsL src2))>>) /\
      (<<IFIV: Coqlib.list_disjoint (name2 (prog_funsL src1)) (name1 (prog_varsL src2))>>) /\
      (<<IVIF: Coqlib.list_disjoint (name1 (prog_varsL src1)) (name2 (prog_funsL src2))>>) /\
      (<<IVIV: Coqlib.list_disjoint (name1 (prog_varsL src1)) (name1 (prog_varsL src2))>>).
  Proof.
    i. apply _link_imp_cond3_ints in _LIC3. des.
    apply Coqlib.list_norepet_app in _LIC3. des.
    repeat split.
    { unfold Coqlib.list_disjoint in *. ii. hexploit _LIC1. eapply H.
      { apply in_app_iff. left; eauto. }
      ii. clarify. }
    { unfold Coqlib.list_disjoint in *. ii. hexploit _LIC1. eapply H.
      { apply in_app_iff. right. apply in_app_iff; right. eauto. }
      ii. clarify. }
    all: clear _LIC1 _LIC3.
    all: apply Coqlib.list_norepet_app in _LIC0; des.
    { clear _LIC0 _LIC1. unfold Coqlib.list_disjoint in *. ii. hexploit _LIC2. eapply H0.
      { apply in_app_iff. left. eapply H. }
      ii. clarify. }
    clear _LIC0 _LIC2. apply Coqlib.list_norepet_app in _LIC1. des.
    unfold Coqlib.list_disjoint in *. ii. hexploit _LIC2; eauto.
  Qed.

  (* Linker for Imp programs *)
  Definition link_imp : option Imp.programL :=
    if (link_imp_cond1 && link_imp_cond2 && link_imp_cond3)
    then Some (mk_programL l_nameL l_evs l_efs l_pvs l_pfs l_publicL l_defsL)
    else None
  .

End LINK.



Section LINKLIST.

  Context `{builtins : builtinsTy}.

  Definition fold_left_option {T} f (t : list T) (opth : option T) :=
    fold_left (fun opt s2 => match opt with | Some s1 => f s1 s2 | None => None end) t opth.

  Lemma fold_left_option_None {T} :
    forall f (l : list T), fold_left_option f l None = None.
  Proof.
    intros f. induction l; ss; clarify.
  Qed.

  Definition fold_right_option {T} f (opt : option T) (l : list T) :=
    fold_right (fun s2 o => match o with | Some s1 => f s2 o | None => None end) opt l.

  Definition fold_right_option_None {T} :
    forall f (l : list T), fold_right_option f None l = None.
  Proof.
    intros f. induction l; ss; clarify. rewrite IHl; ss.
  Qed.

  Fixpoint nlist2list {A} (nl : Coqlib.nlist A) : list A :=
    match nl with
    | Coqlib.nbase a => [a]
    | Coqlib.ncons a nt => a :: (nlist2list nt)
    end.

  Fixpoint list2nlist {A} (a : A) (l : list A) : Coqlib.nlist A :=
    match l with
    | [] => Coqlib.nbase a
    | h :: t => Coqlib.ncons a (list2nlist h t)
    end.

  Lemma n2l_not_nil {A} :
    forall nl, @nlist2list A nl = [] -> False.
  Proof.
    i. induction nl; ss.
  Qed.

  Lemma n2l_cons_exists {A} :
    forall nl a b t (CONS: @nlist2list A nl = a :: b :: t),
      <<EXISTS: exists nt, (nlist2list nt = b :: t) /\ (nl = Coqlib.ncons a nt)>>.
  Proof.
    induction nl; i; ss; clarify.
    destruct t; ss; clarify.
    { exists nl. rewrite H0. ss. }
    eapply IHnl in H0. des. exists nl. split; eauto.
    rewrite H1. ss. rewrite H0. auto.
  Qed.

  Lemma n2l_l2n {A} :
    forall nl,
      (exists (h : A) t, (<<HT: nlist2list nl = h :: t>>) /\ (<<BACK: (list2nlist h t = nl)>>)).
  Proof.
    i. induction nl.
    - exists a, []. ss.
    - ss. des. exists a, (h :: t). ss. rewrite HT. split; ss. red. rewrite BACK. ss.
  Qed.

  Lemma l2n_n2l {A} :
    forall (h : A) t,
      (nlist2list (list2nlist h t)) = h :: t.
  Proof.
    i. depgen h. induction t; i; ss; clarify.
    f_equal. auto.
  Qed.

  Fixpoint link_imp_nlist (src_list : Coqlib.nlist Imp.programL) :=
    match src_list with
    | Coqlib.nbase a => Some a
    | Coqlib.ncons a l =>
      match link_imp_nlist l with
      | Some b => link_imp a b
      | None => None
      end
    end.

  Definition link_imp_list src_list :=
    match src_list with
    | [] => None
    | h :: t => link_imp_nlist (list2nlist h t)
    end.

  Definition link_imps (src_list: list Imp.program) := link_imp_list (List.map lift src_list).

End LINKLIST.

Coercion nlist2list : Coqlib.nlist >-> list.
