Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import Weakening.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Require Import Mem0 Mem1 Main0 Main1.




Section AUX________REMOVEME_____REDUNDANT.

  Context `{Σ: GRA.t}.

  Definition refines_closed (md_tgt md_src: ModL.t): Prop :=
    Beh.of_program (ModL.compile md_tgt) <1= Beh.of_program (ModL.compile md_src)
  .

  Lemma refines_close: SimModSem.refines <2= refines_closed.
  Proof. ii. specialize (PR nil). ss. unfold Mod.add_list in *. ss. rewrite ! ModL.add_empty_l in PR. eauto. Qed.

  Definition add_list (ms: list ModL.t): ModL.t := fold_right ModL.add ModL.empty ms.

  Global Program Instance refines_closed_PreOrder: PreOrder refines_closed.
  Next Obligation. ii; ss. Qed.
  Next Obligation. ii; ss. r in H. r in H0. eauto. Qed.

End AUX________REMOVEME_____REDUNDANT.




Module Mem2.
Section MEM2.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Definition MemSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fsb) => (fn, fun_to_tgt (MainStb++MemStb) fn fsb)) MemSbtb;
    ModSem.mn := "Mem";
    ModSem.initial_mr := (GRA.embed (Auth.black (M:=Mem1._memRA) ε));
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Mem: Mod.t := {|
    Mod.get_modsem := fun _ => MemSem;
    Mod.sk := List.map (fun '(n, _) => (n, Sk.Gfun)) MemStb;
  |}
  .

End MEM2.
End Mem2.




Section WEAKENING.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Require Import Logic TODOYJ.
  Let weaken: forall (fn fn_tgt : string) (fsp_tgt : fspec),
      find (fun '(_fn, _) => dec fn _fn) MemStb = Some (fn_tgt, fsp_tgt) ->
      exists (fn_src : string) (fsp_src : fspec),
        (<< _ : find (fun '(_fn, _) => dec fn _fn) (MainStb ++ MemStb) = Some (fn_src, fsp_src) >>) /\ << _ : fspec_weaker fsp_tgt fsp_src >>
  .
  Proof.
    ii. stb_tac. des_ifs.
    - des_sumbool. subst. esplits; eauto. { stb_tac. ss. } refl.
    - des_sumbool. subst. esplits; eauto. { stb_tac. ss. } refl.
    - des_sumbool. subst. esplits; eauto. { stb_tac. ss. } refl.
    - des_sumbool. subst. esplits; eauto. { stb_tac. ss. } refl.
    - des_sumbool. subst. esplits; eauto. { stb_tac. ss. } refl.
  Qed.

  Theorem Mem12correct: SimModSem.ModSemPair.sim Mem2.MemSem Mem1.MemSem.
  Proof.
    econs.
    { econs.
      { r. split.
        { cbn. unfold RelationPairs.RelCompFun. cbn. refl. }
        eapply weakening_fn; try refl.
        { eapply weaken. }
      }
      econs.
      { r. split.
        { cbn. unfold RelationPairs.RelCompFun. cbn. refl. }
        eapply weakening_fn; try refl.
        { eapply weaken. }
      }
      econs.
      { r. split.
        { cbn. unfold RelationPairs.RelCompFun. cbn. refl. }
        eapply weakening_fn; try refl.
        { eapply weaken. }
      }
      econs.
      { r. split.
        { cbn. unfold RelationPairs.RelCompFun. cbn. refl. }
        eapply weakening_fn; try refl.
        { eapply weaken. }
      }
      econs.
      { r. split.
        { cbn. unfold RelationPairs.RelCompFun. cbn. refl. }
        eapply weakening_fn; try refl.
        { eapply weaken. }
      }
      econs.
    }
    { ss. }
    { ss. esplits; eauto. }
  Qed.

End WEAKENING.






Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Definition MemMain0: ModL.t := ModL.add Mem0.Mem Main0.Main.
  Definition MemMain1: ModL.t := ModL.add Mem2.Mem Main1.Main.

  (* Definition MainSem2: ModSemL.t := {| *)
  (*   ModSemL.fnsems := List.map (map_snd fun_to_src) MainStb; *)
  (*   ModSemL.initial_mrs := [("Main", ε)]; *)
  (* |} *)
  (* . *)

  (* Definition Main2: Mod.t := {| *)
  (*   Mod.get_modsem := fun _ => MainSem2; *)
  (*   Mod.sk := Sk.unit; *)
  (* |} *)
  (* . *)

  (* Definition MemSem2: ModSemL.t := {| *)
  (*   ModSemL.fnsems := List.map (map_snd fun_to_src) MemStb; *)
  (*   ModSemL.initial_mrs := [("Mem", ε)]; *)
  (* |} *)
  (* . *)

  (* Definition Mem2: Mod.t := {| *)
  (*   Mod.get_modsem := fun _ => MemSem2; (*** TODO: we need proper handling of function pointers ***) *)
  (*   Mod.sk := Sk.unit; *)
  (* |} *)
  (* . *)

  (* Definition MemMain2: Mod.t := Mod.add Mem2 Main2. *)

  Definition MemMain2: ModL.t := {|
    ModL.get_modsem := fun _ => {|
        ModSemL.fnsems := List.map (fun '(fn, sb) => (fn, (transl_all sb.(fsb_fspec).(mn)) <*> fun_to_src sb.(fsb_body))) (MemSbtb ++ MainSbtb);
        (* ModSemL.initial_mrs := [("Mem", ε) ; ("Main", ε)]; *)
        ModSemL.initial_mrs := [("Mem", (ε, tt↑)) ; ("Main", (ε, tt↑))];
      |};
    ModL.sk := Sk.unit;
  |}
  .

  Theorem correct: refines_closed MemMain1 MemMain2.
  Proof.
    r.
    set (global_sbtb:=MemSbtb++MainSbtb).
    Local Opaque MemSbtb.
    Local Opaque MainSbtb.
    eapply adequacy_type with (sbtb:=global_sbtb).
    { unfold compose. cbn. f_equal.
    eapply adequacy_type.
  Qed.

  Theorem embed_wf
          A
          `{@GRA.inG A Σ}
          (a: A)
          (WF: URA.wf a)
    :
      URA.wf (GRA.embed a)
  .
  Proof.
    ss. ii. unfold GRA.embed.
    Local Transparent GRA.to_URA. ur. i. des_ifs; cycle 1.
    { apply URA.wf_unit. }
    ss. unfold PCM.GRA.cast_ra, eq_rect, eq_sym. destruct GRA.inG_prf. ss.
    Local Opaque GRA.to_URA.
  Qed.

  (* Definition incl (sbtb0 sbtb1: list (string * fspec)): Prop := List.incl  *)
  (* Lemma handle_hCallE_tgt_ext *)
  (*       sbtb0 sbtb1 mn cur *)
  (*   : *)
  (*     (handle_hCallE_tgt sbtb0 mn cur) = (handle_hCallE_tgt sbtb1 mn cur) *)
  (* . *)
  (* Proof. *)
  (*   unfold handle_hCallE_tgt. repeat (apply func_ext_dep; i). des_ifs. *)
  (*   - *)
  (* Qed. *)

  (* Let body_to_tgt_aux: forall E R1 R2 RR *)
  (*     AR sbtb0 sbtb1 mn cur *)
  (*     (bd: itree (hCallE +' pE +' eventE) AR) *)
  (*     i_src i_tgt *)
  (*     (SRC: i_src ~= (interp_hCallE_tgt sbtb0 mn cur bd)) *)
  (*     (TGT: i_tgt ~= (interp_hCallE_tgt sbtb1 mn cur bd)) *)
  (*   , *)
  (*     @eq_itree E R1 R2 RR i_src i_tgt *)
  (* (* ≅  *) *)
  (* . *)
  (* Proof. *)
  (*   ginit. *)
  (*   ecofix CIH. *)
  (* Qed. *)
  (* Unset Universe Checking. *)



  (*********** TODO: finish the theory and move to proper place ***********)
  Definition contains R (stb: list (string * fspec)) (body: itree (hCallE +' pE +' eventE) R): Prop :=
    admit "fspecbody's body calls only the functions that are inside stb"
  .

  Definition extends (stb0 stb1: list (string * fspec)): Prop :=
    (* admit "stb1 has more entries" *)
    List.incl stb0 stb1
  .

  Lemma interp_hCallE_tgt_ext
        AR
        stb0 stb1 mn cur (body: itree (hCallE +' pE +' eventE) AR)
        (A: contains stb0 body)
        (B: extends stb0 stb1)
    :
      interp_hCallE_tgt stb0 mn cur body = interp_hCallE_tgt stb1 mn cur body
  .
  Proof.
    f. ginit. revert_until Σ. gcofix CIH. i.
    unfold interp_hCallE_tgt.
    ides body;  rewrite ! unfold_interp; ired; ss.
    - gstep. econs; et.
    - gstep. econs; et. gbase. eapply CIH; ss.
    - guclo eqit_clo_bind. econs.
      + instantiate (1:=eq). destruct e.
        { (**** main part ****)
          ired. unfold handle_hCallE_tgt.
          unfold unwrapN. des_ifs.
          - assert(T: p = p0) by admit "ez - uniqueness". subst. refl.
          - exfalso. admit "ez - extends".
          - exfalso. admit "ez - contains".
          - exfalso. admit "ez - contains".
        }
        destruct s; ss.
        { destruct p; ss; ired; refl. }
        { destruct e; ss; ired; refl. }
      + ii. clarify. gstep. econs; eauto. gbase. eapply CIH; et.
  Unshelve.
    all: try (by econs).
  Qed.

  Lemma body_to_tgt_ext
        AA AR
        stb0 stb1 mn cur (body: (AA -> itree (hCallE +' pE +' eventE) AR)) varg
        (A: contains stb0 (body varg))
        (B: extends stb0 stb1)
    :
      body_to_tgt stb0 mn cur body varg = body_to_tgt stb1 mn cur body varg
  .
  Proof. eapply interp_hCallE_tgt_ext; et. Qed.

  Lemma fun_to_tgt_ext
        stb0 stb1 fn sb
        (A: forall varg, contains stb0 (sb.(fsb_body) varg))
        (B: extends stb0 stb1)
    :
      fun_to_tgt stb0 fn sb = fun_to_tgt stb1 fn sb
  .
  Proof.
    unfold fun_to_tgt. unfold HoareFun. apply func_ext. i. grind.
    erewrite body_to_tgt_ext; et. grind.
    erewrite interp_hCallE_tgt_ext; et. eapply A; et.
  Unshelve.
    all: ss.
  Qed.

  (* Lemma map_ext *)
  (*       A B *)
  (*       l (f g : A -> B) *)
  (*       (EXT: forall a, In a l -> f a = g a) *)
  (*   : *)
  (*     List.map f l = List.map g l *)
  (* . *)
  (* Proof. *)
  (*   clear Σ H. *)
  (*   ginduction l; ii; ss. f_equal. *)
  (*   - eapply EXT; et. *)
  (*   - eapply IHl; et. *)
  (* Qed. *)

  Theorem correct: Beh.of_program (Mod.compile MemMain1) <1= Beh.of_program (Mod.compile MemMain2).
  Proof.
    ii.
    set (global_sbtb:=MemSbtb++MainSbtb).
    (* clearbody global_stb. *)
    Local Opaque MemSbtb.
    Local Opaque MainSbtb.
    eapply adequacy_type with (sbtb:=global_sbtb) in PR.
    { ss. }
    { cbn. unfold global_sbtb. rewrite List.map_app.
      Set Printing Coercions.
      seal fun_to_tgt. (*** without this, other tactics (des_ifs; refl; ss; f_equal; etc) will take infinite time. Opaque does help here at all. ***)
      f_equal; cycle 1.
      { autounfold with stb; autorewrite with stb; refl. }
      apply map_ext. (*** better than just "f_equal" ***)
      i. des_ifs. r; f_equal. unseal fun_to_tgt. eapply fun_to_tgt_ext.
      - ii. ss.
        Local Transparent MemSbtb. cbn in IN. Local Opaque MemSbtb. des; ss; clarify; ss.
        + admit "ez".
        + admit "ez".
        + admit "ez".
        + admit "ez".
        + admit "ez".
      - admit "ez".
    }
    { Local Transparent MemSbtb. cbn. Local Opaque MemSbtb. des_ifs; ss. }
    ss. unfold compose. ss. rewrite ! URA.unit_id. rewrite ! URA.unit_idl.
    eapply embed_wf; et.
    assert(@URA.wf (Mem1._memRA) (fun b ofs => if (b =? 0)%nat && (ofs =? 0)%Z then Excl.just Vundef else Excl.unit)).
    { repeat ur. i; des_ifs. }
    admit "EZ -- add black wf lemma".
  Qed.

End PROOF.
