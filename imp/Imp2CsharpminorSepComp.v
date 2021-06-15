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

  Context `{Σ: GRA.t}.

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
