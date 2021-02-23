Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem SimModSem.

Require Import FunctionalExtensionality.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.


(* TODO: move to Module Mod *)
Section MOD.

  Context `{Σ: GRA.t}.

  Definition Mod_empty: Mod.t :=
    {|
    Mod.get_modsem := fun _ => ModSem.mk [] [];
    Mod.sk := Sk.unit;
    |}
  .

  Lemma add_empty_l md: Mod.add md Mod_empty = md.
  Proof.
    destruct md; ss.
    unfold Mod.add, ModSem.add. f_equal; ss.
    - extensionality skenv. destruct (get_modsem skenv); ss.
      repeat rewrite app_nil_r. auto.
    - unfold Sk.add. rewrite app_nil_r. auto.
  Qed.

  Lemma add_empty_r md: Mod.add Mod_empty md = md.
  Proof.
    destruct md; ss.
    unfold Mod.add, ModSem.add. f_equal; ss.
    extensionality skenv. destruct (get_modsem skenv); ss.
  Qed.

  Fixpoint add_list (mds: list Mod.t): Mod.t :=
    match mds with
    | hd::tl => Mod.add hd (add_list tl)
    | [] => Mod_empty
    end.

  Theorem adequacy_local_closed (md_src md_tgt: Mod.t)
          (SIM: ModPair.sim md_src md_tgt)
    :
      Beh.of_program (Mod.interp md_tgt) <1=
      Beh.of_program (Mod.interp md_src).
  Proof.
    hexploit ModPair.adequacy_local.
    { eauto. }
    i. specialize (H Mod_empty). repeat rewrite add_empty_r in *. auto.
  Qed.

  Lemma sim_list_adequacy (mds_src mds_tgt: list Mod.t)
        (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt)
    :
      <<CR: forall ctx, Beh.of_program (Mod.interp (Mod.add ctx (add_list mds_tgt))) <1=
                        Beh.of_program (Mod.interp (Mod.add ctx (add_list mds_src)))>>.
  Proof.
    induction FORALL; ss.
    cut (forall ctx,
            Beh.of_program (Mod.interp (Mod.add ctx (Mod.add y (add_list l')))) <1=
            Beh.of_program (Mod.interp (Mod.add ctx (Mod.add y (add_list l))))).
    { ii. eapply H0 in PR.
      apply Mod.add_comm in PR. apply Mod.add_comm.
      erewrite <- Mod.add_assoc in *.
      apply Mod.add_comm in PR. apply Mod.add_comm.
      eapply ModPair.adequacy_local.
      { eauto. }
      { eapply PR. }
    }
    { i. erewrite Mod.add_assoc in *. eapply IHFORALL. auto. }
  Qed.

  Lemma sim_list_adequacy_closed (mds_src mds_tgt: list Mod.t)
        (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt)
    :
      Beh.of_program (Mod.interp (add_list mds_tgt)) <1=
      Beh.of_program (Mod.interp (add_list mds_src)).
  Proof.
    hexploit sim_list_adequacy.
    { eauto. }
    i. specialize (H Mod_empty). repeat rewrite add_empty_r in *. auto.
  Qed.

End MOD.
