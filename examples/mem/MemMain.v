Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Require Import Mem1 Main1.

Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Definition MemMain1: Mod.t := Mod.add Mem Main.

  (* Definition MainSem2: ModSem.t := {| *)
  (*   ModSem.fnsems := List.map (map_snd fun_to_src) MainStb; *)
  (*   ModSem.initial_mrs := [("Main", ε)]; *)
  (* |} *)
  (* . *)

  (* Definition Main2: Mod.t := {| *)
  (*   Mod.get_modsem := fun _ => MainSem2; *)
  (*   Mod.sk := Sk.unit; *)
  (* |} *)
  (* . *)

  (* Definition MemSem2: ModSem.t := {| *)
  (*   ModSem.fnsems := List.map (map_snd fun_to_src) MemStb; *)
  (*   ModSem.initial_mrs := [("Mem", ε)]; *)
  (* |} *)
  (* . *)

  (* Definition Mem2: Mod.t := {| *)
  (*   Mod.get_modsem := fun _ => MemSem2; (*** TODO: we need proper handling of function pointers ***) *)
  (*   Mod.sk := Sk.unit; *)
  (* |} *)
  (* . *)

  (* Definition MemMain2: Mod.t := Mod.add Mem2 Main2. *)

  Definition MemMain2: Mod.t := {|
    Mod.get_modsem := fun _ => {|
        ModSem.fnsems := List.map (fun '(fn, sb) => (fn, fun_to_src sb.(fsb_body))) (MemSbtb ++ MainSbtb);
        (* ModSem.initial_mrs := [("Mem", ε) ; ("Main", ε)]; *)
        ModSem.initial_mrs := [("Mem", (ε, tt↑)) ; ("Main", (ε, tt↑))];
      |};
    Mod.sk := Sk.unit;
  |}
  .

  Theorem padding_wf
          A
          `{@GRA.inG A Σ}
          (a: A)
          (WF: URA.wf a)
    :
      URA.wf (GRA.padding a)
  .
  Proof.
    ss. ii. unfold GRA.padding.
    Local Transparent GRA.to_URA. ss. i. des_ifs; cycle 1.
    { apply URA.wf_unit. }
    ss. unfold PCM.GRA.cast_ra, eq_rect, eq_sym. destruct GRA.inG_prf. ss.
    Local Opaque GRA.to_URA.
  Qed.

  Infix "⋅" := URA.add (at level 50, left associativity).
  Notation "(⋅)" := URA.add (only parsing).

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
          des_ifs.
          - assert(T: s = s0 /\ f = f0) by admit "ez - uniqueness". destruct T. subst. refl.
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

  Theorem correct: Beh.of_program (Mod.interp MemMain1) <1= Beh.of_program (Mod.interp MemMain2).
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
    eapply padding_wf; et. ss. esplits; et.
    { rr. esplits; et. ss. }
    { i. des_ifs. }
  Qed.

End PROOF.
