Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import BoxHeader Box1 BoxMain1.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG boxRA Σ}.

  Definition BoxMain1: Mod.t := Mod.add Box Main.

  Definition BoxMain2: Mod.t := {|
    Mod.get_modsem := fun _ => {|
        ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_src body)) (BoxFtb ++ MainFtb);
        ModSem.initial_mrs := [];
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
    ss. ii. unfold GRA.padding.  des_ifs; cycle 1.
    { apply URA.wf_unit. }
    ss. unfold PCM.GRA.cast_ra, eq_rect, eq_sym. destruct GRA.inG_prf. ss.
  Qed.

  Local Opaque GRA.to_URA.
  Infix "⋅" := URA.add (at level 50, left associativity).
  Notation "(⋅)" := URA.add (only parsing).
  (* Local Opaque URA.add. *)

  Theorem correct: Beh.of_program (Mod.interp BoxMain1) <1= Beh.of_program (Mod.interp BoxMain2).
  Proof.
    ii.
    set (global_ftb:=BoxFtb++MainFtb).
    set (global_stb:=BoxStb++MainStb).
    (* clearbody global_stb. *)
    Local Opaque BoxStb.
    Local Opaque MainStb.
    eapply adequacy_type with (stb:=global_stb) (ftb:=global_ftb) in PR. cbn in *.
    rp; try apply PR; cycle 1.
    { refl. }
    { clear PR. f_equal. }
    { ss. f_equal.
      { admit "ez". }
      f_equal.
      { admit "ez". }
      f_equal.
      { admit "ez". }
    }
    { ss. }
    { ss. Hint Unfold ε. try rewrite URA.unit_id.
      unfold ε. rewrite ! URA.unit_id. rewrite ! URA.unit_idl.
      unfold compose. des_ifs. des_sumbool. ss. clear_tac.
      unfold library, client.
      rewrite GRA.padding_add.
      ss.
      assert(A: URA.wf (t:=boxRA) (URA.excl (M:=BoxHeader._boxRA) (inl (Some 0%Z)) (inl (Some 0%Z)))).
      { ss. esplits; ss; et. rr. exists URA.unit. ss. }
      abstr (URA.excl (M:=BoxHeader._boxRA) (inl (Some 0%Z)) (inl (Some 0%Z))) r.
      clear - A.
      eapply padding_wf; et.
    }
  Qed.

End PROOF.
