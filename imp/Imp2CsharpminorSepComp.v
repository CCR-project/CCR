From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory Csharpminor Linking.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.
Require Import Imp2Csharpminor.
Require Import ImpProofs.
Require Import SimSTS2.
Require Import Mem0.
Require Import IRed.

Require Import Imp2CsharpminorMatch.
Require Import Imp2CsharpminorArith.
Require Import Imp2CsharpminorGenv.
Require Import Imp2CsharpminorMem.
Require Import Imp2CsharpminorLink.
Require Import Imp2CsharpminorSim.

Set Implicit Arguments.

Section PROOFALL.

  Import Maps.PTree.

  Context `{Σ: GRA.t}.

  Definition get_sge (src : Imp.programL) := Sk.load_skenv (Sk.sort (ImpMod.get_modL src).(ModL.sk)).
  Definition get_tge (tgt : Csharpminor.program) := Genv.globalenv tgt.

  Definition dummy_blk : positive := 1%positive.

  Definition map_blk : programL -> nat -> Values.block :=
    fun src blk =>
      match (compile src) with
      | OK tgt =>
        if (ge_dec blk (src_init_nb src)) then Pos.of_succ_nat (2 + (ext_len src) + blk)
        else
          let sg := get_sge src in
          let tg := get_tge tgt in
          match sg.(SkEnv.blk2id) blk with
          | Some name =>
            match Genv.find_symbol tg (s2p name) with
            | Some tblk => tblk
            | None => dummy_blk
            end
          | None => dummy_blk
          end
      | _ => dummy_blk
      end
  .

  Lemma map_blk_after_init :
    forall src blk
      (COMP : exists tgt, Imp2Csharpminor.compile src = OK tgt)
      (ALLOCED : blk >= (src_init_nb src)),
      (<<ALLOCMAP: (map_blk src blk) = Pos.of_succ_nat (2 + (ext_len src) + blk)>>).
  Proof.
    i. unfold map_blk. des. des_ifs.
  Qed.

  Lemma gmap_preserves_length :
    forall src gm
      (GAMP: get_gmap src = Some gm),
      (<<EVL: List.length gm.(_ext_vars) = List.length src.(ext_varsL)>>) /\
      (<<EFL: List.length gm.(_ext_funs) = List.length src.(ext_funsL)>>) /\
      (<<IVL: List.length gm.(_int_vars) = List.length src.(prog_varsL)>>) /\
      (<<IFL: List.length gm.(_int_funs) = List.length src.(prog_funsL)>>).
  Proof.
    unfold get_gmap. i. uo; des_ifs; ss. repeat split.
    - unfold compile_eVars. eapply map_length.
    - unfold compile_eFuns. eapply map_length.
    - unfold compile_iVars. eapply map_length.
    - unfold pre_compile_iFuns in Heq0. des_ifs. do 2 (rewrite List.map_map). eapply map_length.
  Qed.

  Lemma Genv_advance_next_length :
    forall (l : list (ident * globdef fundef ())) p,
      <<LEN: Genv.advance_next l p = Pos.of_nat ((List.length l) + (Pos.to_nat p))>>.
  Proof.
    i. depgen p. induction l; i; ss; clarify.
    - sym; apply Pos2Nat.id.
    - rewrite IHl. rewrite Pos2Nat.inj_succ. rewrite <- plus_n_Sm. ss.
  Qed.

  Lemma NoDup_norepeat :
    forall A (l : list A), <<NOREPET: Coqlib.list_norepet l>> <-> NoDup l.
  Proof.
    split; induction l; i; ss; eauto.
    - econs.
    - inv H. econs; eauto.
    - econs.
    - inv H. econs; eauto. eapply IHl; eauto.
  Qed.

  Lemma perm_elements_PTree_norepeat :
    forall A (l : list (elt * A))
      (NOREPET: Coqlib.list_norepet (List.map fst l)),
      <<LEN: Permutation.Permutation (elements (Maps.PTree_Properties.of_list l)) l>>.
  Proof.
    i. eapply Permutation.NoDup_Permutation.
    - apply NoDup_map_inv with (f:= fst). apply NoDup_norepeat. eapply elements_keys_norepet.
    - apply NoDup_map_inv with (f:= fst). apply NoDup_norepeat. auto.
    - i. assert (NOREPET2: Coqlib.list_norepet (List.map fst (elements (Maps.PTree_Properties.of_list l)))).
      { eapply elements_keys_norepet. }
      destruct x as [ID NODE]. split; i.
      + hexploit Maps.PTree_Properties.of_list_norepet.
        { eapply NOREPET2. }
        { eapply H. }
        i. rewrite Maps.PTree_Properties.of_list_elements in H0. eapply Maps.PTree_Properties.in_of_list in H0. auto.
      + hexploit Maps.PTree_Properties.of_list_norepet.
        { eapply NOREPET. }
        { eapply H. }
        i. eapply Maps.PTree_Properties.in_of_list. rewrite Maps.PTree_Properties.of_list_elements. auto.
  Qed.

  Lemma length_elements_PTree_norepet :
    forall A (l : list (elt * A))
      (NOREPET: Coqlib.list_norepet (List.map fst l)),
      <<LEN: List.length (elements (Maps.PTree_Properties.of_list l)) = List.length l>>.
  Proof.
    i. eapply Permutation.Permutation_length. eapply perm_elements_PTree_norepeat. auto.
  Qed.

  Lemma get_iFuns_length :
    forall g l1 l2 (GET: get_iFuns g l1 = Some l2), List.length l1 = List.length l2.
  Proof.
    i. unfold get_iFuns in GET. des_ifs. rewrite List.map_map. sym; eapply map_length.
  Qed.

  Lemma wfprog_defsL_length :
    forall src
      (WFPROG: Permutation.Permutation
                 ((List.map fst src.(prog_varsL)) ++ (List.map (compose fst snd) src.(prog_funsL)))
                 (List.map fst src.(defsL))),
      <<DEFSL: List.length src.(defsL) = List.length src.(prog_varsL) + List.length src.(prog_funsL)>>.
  Proof.
    i. unfold compose in *. do 2 rewrite <- (map_length fst). rewrite <- (map_length (compose fst snd)).
    rewrite <- app_length. eapply Permutation.Permutation_length. apply Permutation.Permutation_sym. auto.
  Qed.

  Lemma map_blk_init_range :
    forall src tgt id b
      (COMP : Imp2Csharpminor.compile src = OK tgt)
      (WFPROG: Permutation.Permutation
                 ((List.map fst src.(prog_varsL)) ++ (List.map (compose fst snd) src.(prog_funsL)))
                 (List.map fst src.(defsL)))
      (TGT: Genv.find_symbol (get_tge tgt) id = Some b),
      <<RANGE: (b < (tgt_init_nb src))%positive>>.
  Proof.
    i. unfold get_tge in *. unfold compile, _compile in COMP. des_ifs. unfold compile_gdefs in Heq0.
    uo; des_ifs; ss. unfold Genv.find_symbol in TGT. apply Genv.genv_symb_range in TGT.
    unfold Genv.globalenv in TGT. ss. rewrite Genv.genv_next_add_globals in TGT. ss.
    unfold tgt_init_nb. unfold ext_len, int_len. hexploit gmap_preserves_length; eauto. i; des.
    rewrite Genv_advance_next_length in TGT. rewrite length_elements_PTree_norepet in TGT; eauto.
    rewrite wfprog_defsL_length; auto. repeat rewrite app_length in TGT. ss. rewrite app_length in TGT.
    eapply get_iFuns_length in Heq0. rewrite <- Heq0 in TGT.
    repeat rewrite map_length in TGT.
    rewrite EVL in TGT; rewrite EFL in TGT; rewrite IVL in TGT; rewrite IFL in TGT.
    depgen TGT. clear. i. unfold NW.
    match goal with
    | [ TGT: Coqlib.Plt _ ?l1 |- (_ < ?l2)%positive ] => replace l2 with l1; eauto
    end.
    lia.
  Qed.

  Lemma compiled_then_exists:
    forall src gm l symb  
      (GMAP: get_gmap src = Some gm)
      (COMP : compile_gdefs gm src = Some l)
      (NOREPET : Coqlib.list_norepet (List.map fst l))
      (WFPROG : In symb (List.map fst (prog_varsL src) ++ List.map (compose fst snd) (prog_funsL src))),
    exists gd : globdef fundef (), In (s2p symb, gd) l.
  Proof.
    i. apply in_app_or in WFPROG. des.
    - apply Coqlib.list_in_map_inv in WFPROG. des. destruct x as [vn v].
      unfold compile_gdefs in COMP. uo; des_ifs; ss.
      hexploit exists_compiled_variable; eauto. i; des. exists (Gvar cv).
      apply in_or_app. right. apply in_or_app. right. ss. do 2 right. apply in_or_app; right.
      clear WFPROG0.
      match goal with
      | [ H : In ?y _ |- (In ?x (List.map ?f _)) ] => set (mapf:=f) in *; replace x with (mapf y)
      end.
      2:{ subst mapf. unfold lift_def. ss. }
      apply in_map. auto.
    - apply Coqlib.list_in_map_inv in WFPROG. des. destruct x as [mn [fn impf]].
      unfold compile_gdefs in COMP. uo; des_ifs; ss.
      hexploit exists_compiled_function; eauto. i; des. exists (Gfun (Internal cf)).
      apply in_or_app. right. apply in_or_app. right. ss. do 2 right. apply in_or_app; left; eauto.
  Qed.

  Lemma in_src_in_tgt :
    forall src gm (l: list (ident * globdef fundef ())) symb
      (GMAP: get_gmap src = Some gm)
      (COMP: compile_gdefs gm src = Some l)
      (NOREPET: Coqlib.list_norepet (List.map fst l))
      (WFPROG : In symb (List.map fst (prog_varsL src) ++ List.map (compose fst snd) (prog_funsL src))),
      <<EXISTSIN: exists gd, In (s2p symb, gd) (elements (Maps.PTree_Properties.of_list l))>>.
  Proof.
    i. unfold get_gmap in GMAP. uo; des_ifs; ss.
    assert (NOREPET2: Coqlib.list_norepet (List.map fst l)); auto.
    apply perm_elements_PTree_norepeat in NOREPET. apply Permutation.Permutation_sym in NOREPET.
    assert (IN1: exists gd, In (s2p symb, gd) l).
    { eapply compiled_then_exists; eauto. unfold get_gmap. uo; des_ifs; ss. }
    des. exists gd. 
    eapply Permutation.Permutation_in; eauto.
  Qed.

  Lemma found_in_src_in_tgt :
    forall src tgt blk symb
      (COMP: compile src = OK tgt)
      (WFPROG: Permutation.Permutation
                 ((List.map fst src.(prog_varsL)) ++ (List.map (compose fst snd) src.(prog_funsL)))
                 (List.map fst src.(defsL)))
      (SRC: SkEnv.blk2id (get_sge src) blk = Some symb),
      <<TGTFOUND: exists tb, Genv.find_symbol (get_tge tgt) (s2p symb) = Some tb>>.
  Proof.
    i. unfold compile, _compile in COMP. des_ifs. unfold get_sge, get_tge in *. ss.
    eapply Sk.in_env_in_sk in SRC. des. eapply Sk.sort_incl_rev in SRC.
    apply Permutation.Permutation_sym in WFPROG. apply (in_map fst) in SRC. ss.
    eapply Permutation.Permutation_in in WFPROG; eauto. clear SRC def.
    rename Heq into GMAP. rename Heq0 into COMPGDEFS. rename l0 into NOREPET.
    hexploit in_src_in_tgt; eauto. i. des.
    eapply Genv.find_symbol_exists. ss. eapply H.
  Qed.

  Lemma sksort_same_len :
    forall l, <<LEN: Datatypes.length l = Datatypes.length (Sk.sort l)>>.
  Proof.
    i. pose (Sk.SkSort.Permuted_sort l) as SORTED. apply Permutation.Permutation_length in SORTED. eauto.
  Qed.

  Lemma map_blk_neq :
    forall src b1 b2
      (COMP : exists tgt, Imp2Csharpminor.compile src = OK tgt)
      (WFPROG: Permutation.Permutation
                 ((List.map fst src.(prog_varsL)) ++ (List.map (compose fst snd) src.(prog_funsL)))
                 (List.map fst src.(defsL)))
      (BLK1: b1 >= (src_init_nb src))
      (BLK2: ~ (b2 >= (src_init_nb src))),
      map_blk src b1 <> map_blk src b2.
  Proof.
    i. unfold map_blk. des_ifs; ii; rename H into CONTRA.
    - clear g n. assert (RANGE: (b < (tgt_init_nb src))%positive).
      { eapply map_blk_init_range; eauto. }
      unfold tgt_init_nb in RANGE. unfold src_init_nb in *. lia.
    - clear g n. unfold get_sge, get_tge in *. hexploit found_in_src_in_tgt; eauto. i; des. unfold get_tge in H; clarify.
    - clear g n. unfold get_sge in Heq0. apply not_ge in BLK2. rename Heq0 into NOTFOUND. simpl in NOTFOUND.
      unfold src_init_nb in BLK2. unfold int_len in BLK2.
      assert (SORTED: b2 < Datatypes.length (Sk.sort (defsL src))).
      { rewrite <- sksort_same_len. ss. }
      eapply Sk.env_range_some in SORTED. des. setoid_rewrite SORTED in NOTFOUND. clarify.
    - des. clarify.
  Qed.

  Lemma map_blk_inj :
    forall src b1 b2
      (COMP : exists tgt, Imp2Csharpminor.compile src = OK tgt)
      (WFPROG: Permutation.Permutation
                 ((List.map fst src.(prog_varsL)) ++ (List.map (compose fst snd) src.(prog_funsL)))
                 (List.map fst src.(defsL))),
      <<INJ: map_blk src b1 = map_blk src b2 -> b1 = b2>>.
  Proof.
    i. des. destruct (ge_dec b1 (src_init_nb src)) eqn:BRANGE1; destruct (ge_dec b2 (src_init_nb src)) eqn:BRANGE2.
    { unfold map_blk. des_ifs. ii. lia. }
    { hexploit map_blk_neq; eauto; ii; clarify. }
    { hexploit map_blk_neq; eauto; ii. sym in H0. clarify. }
    unfold map_blk. unfold src_init_nb in *. unfold int_len in *. unfold get_sge in *.
    rewrite BRANGE1. rewrite BRANGE2. clear BRANGE1 BRANGE2.
    rename n into BLK1. apply not_ge in BLK1. rename n0 into BLK2. apply not_ge in BLK2.
    assert (SBLK1: b1 < Datatypes.length (Sk.sort (defsL src))).
    { rewrite <- sksort_same_len; ss. }
    assert (SBLK2: b2 < Datatypes.length (Sk.sort (defsL src))).
    { rewrite <- sksort_same_len; ss. }
    eapply Sk.env_range_some in SBLK1. eapply Sk.env_range_some in SBLK2. des.
    ss. rewrite SBLK1. rewrite SBLK2. rewrite COMP. ii.
    hexploit found_in_src_in_tgt.
    1,2: eauto.
    { unfold get_sge. ss. eapply SBLK1. }
    hexploit found_in_src_in_tgt.
    1,2: eauto.
    { unfold get_sge. ss. eapply SBLK2. }
    i. des. rewrite H0 in H. rewrite H1 in H. clarify.
    apply Genv.find_invert_symbol in H0. apply Genv.find_invert_symbol in H1.
    rewrite H1 in H0. clear H1. clarify. apply s2p_inj in H0. clarify.
    
    { eauto. }


  Admitted.






  (* Lemma list_norepet_NoDupB {K} {decK} : *)
  (*   forall l, Coqlib.list_norepet l <-> @NoDupB K decK l = true. *)
  (* Proof. *)
  (*   split; i. *)
  (*   - induction H; ss. *)
  (*     clarify. *)
  (*     destruct (in_dec decK hd tl); clarify. *)
  (*   - induction l; ss; clarify. constructor. *)
  (*     des_ifs. econs 2; auto. *)
  (* Qed. *)

  (* Definition wf_imp_prog (src : Imp.programL) := *)
  (*   Coqlib.list_norepet (compile_gdefs (get_gmap src) src). *)

  (* Lemma compile_then_wf : forall src tgt, *)
  (*     compile src = OK tgt *)
  (*     -> *)
  (*     wf_imp_prog src. *)
  (* Proof. *)
  (*   unfold compile, _compile. i. *)
  (*   destruct (compile_gdefs (get_gmap src) src) eqn:EQ; clarify. *)
  (*   eauto using compile_gdefs_then_wf. *)
  (* Qed. *)

  (* Maps.PTree.elements_extensional 
     we will rely on above theorem for commutation lemmas *)
  Lemma _comm_link_imp_compile
        src1 src2 srcl tgt1 tgt2 tgtl
        (COMP1: compile src1 = OK tgt1)
        (COMP2: compile src2 = OK tgt2)
        (LINKSRC: link_imp src1 src2 = Some srcl)
        (LINKTGT: link_prog tgt1 tgt2 = Some tgtl)
    :
      <<COMPL: compile srcl = OK tgtl>>.
  Proof.
  Admitted.

  Definition wf_link {T} (program_list : list T) :=
    exists h t, program_list = h :: t.

  Inductive compile_list :
    list programL -> list (Csharpminor.program) -> Prop :=
  | compile_nil :
      compile_list [] []
  | compile_head
      src_h src_t tgt_h tgt_t
      (COMPH: compile src_h = OK tgt_h)
      (COMPT: compile_list src_t tgt_t)
    :
      <<COMPLIST: compile_list (src_h :: src_t) (tgt_h :: tgt_t)>>.

  Definition fold_left_option {T} f (t : list T) (opth : option T) :=
    fold_left
      (fun opt s2 => match opt with | Some s1 => f s1 s2 | None => None end)
      t opth.

  Lemma fold_left_option_None {T} :
    forall f (l : list T), fold_left_option f l None = None.
  Proof.
    intros f. induction l; ss; clarify.
  Qed.

  Definition link_imp_list src_list :=
    match src_list with
    | [] => None
    | src_h :: src_t =>
      fold_left_option link_imp src_t (Some src_h)
    end.

  Definition link_csm_list (tgt_list : list (Csharpminor.program)) :=
    match tgt_list with
    | [] => None
    | tgt_h :: tgt_t =>
      fold_left_option link_prog tgt_t (Some tgt_h)
    end.

  Lemma comm_link_imp_compile
        src_list srcl tgt_list tgtl
        (COMPL: compile_list src_list tgt_list)
        (LINKSRC: link_imp_list src_list = Some srcl)
        (LINKTGT: link_csm_list tgt_list = Some tgtl)
    :
      compile srcl = OK tgtl.
  Proof.
    i. destruct src_list; destruct tgt_list; ss; clarify.
    inv COMPL; clarify.
    generalize dependent srcl. generalize dependent tgtl.
    generalize dependent p. generalize dependent p0.
    induction COMPT; i; ss; clarify.
    destruct (link_prog p0 tgt_h) eqn:LPt; ss; clarify.
    2:{ rewrite fold_left_option_None in LINKTGT; clarify. }
    destruct (link_imp p src_h) eqn:LPs; ss; clarify.
    2:{ rewrite fold_left_option_None in LINKSRC; clarify. }
    eapply IHCOMPT.
    2: apply LINKTGT.
    2: apply LINKSRC.
    eapply _comm_link_imp_compile.
    3: apply LPs.
    3: apply LPt.
    auto. auto.
  Qed.

  Lemma _comm_link_imp_link_mod
        src1 src2 srcl tgt1 tgt2 tgtl (ctx : ModL.t)
        (MOD1: ImpMod.get_modL src1 = tgt1)
        (MOD2: ImpMod.get_modL src2 = tgt2)
        (LINKIMP: link_imp src1 src2 = Some srcl)
        (MODL: ImpMod.get_modL srcl = tgtl)
    :
      <<LINKMOD: ModL.add (ModL.add ctx tgt1) tgt2 = ModL.add ctx tgtl>>.
  Proof.
  Admitted.

  Lemma comm_link_imp_link_mod
        src_list srcl tgt_list tgtl ctx
        (MODLIST: List.map (fun src => ImpMod.get_modL src) src_list = tgt_list)
        (LINKIMP: link_imp_list src_list = Some srcl)
        (MODL: ImpMod.get_modL srcl = tgtl)
    :
      <<LINKMOD: fold_left ModL.add tgt_list ctx = ModL.add ctx tgtl>>.
  Proof.
    destruct src_list eqn:SL; i; ss; clarify.
    move p after l.
    revert_until Σ.
    induction l; i; ss; clarify.
    destruct (link_imp p a) eqn:LI; ss; clarify.
    2:{ rewrite fold_left_option_None in LINKIMP; clarify. }
    erewrite _comm_link_imp_link_mod; eauto.
  Qed.

  Definition imp_initial_state (src : Imp.programL) :=
    (ModL.compile (ImpMod.get_modL src)).(initial_state).

  Lemma single_compile_behavior_improves
        (src: Imp.programL) (tgt: Csharpminor.program) srcst tgtst
        (COMP: compile src = OK tgt)
        (SINIT: srcst = imp_initial_state src)
        (TINIT: Csharpminor.initial_state tgt tgtst)
    :
      <<IMPROVES: @improves2 _ (Csharpminor.semantics tgt) srcst tgtst>>.
  Proof.
  Admitted.

  Definition src_initial_state (src : ModL.t) :=
    (ModL.compile src).(initial_state).

  Theorem compile_behavior_improves
          (src_list : list Imp.program) srcl tgt_list tgtl srcst tgtst
          (COMP: let src_list_lift := List.map Imp.lift src_list in
                 compile_list src_list_lift tgt_list)
          (LINKSRC: let src_list_mod := List.map ImpMod.get_mod src_list in
                    Mod.add_list (Mem :: src_list_mod) = srcl)
          (LINKTGT: link_csm_list tgt_list = Some tgtl)
          (SINIT: srcst = src_initial_state srcl)
          (TINIT: Csharpminor.initial_state tgtl tgtst)
    :
      <<IMPROVES: @improves2 _ (Csharpminor.semantics tgtl) srcst tgtst>>.
  Proof.
  Admitted.

End PROOFALL.
