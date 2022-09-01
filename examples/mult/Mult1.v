Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import MultHeader.

Set Implicit Arguments.



Section PROOF.
  Context `{@GRA.inG fRA Σ}.
  Context `{@GRA.inG gRA Σ}.
  Context `{@GRA.inG hRA Σ}.

  Definition multSbtb: list (gname * fspecbody) :=
    [("feasy", mk_specbody f_spec0 (fun _ => Ret Vundef↑));
    ("fhard", mk_specbody f_spec1 (fun _ => `_: val <- ccallU "g" tt;; `_: val <- ccallU "h" tt;; Ret Vundef↑));
    ("apc", mk_specbody f_spec0 (fun _ => _ <- Ret Vundef;;; Ret Vundef↑))
    ].

  Definition SMultSem: SModSem.t := {|
    SModSem.fnsems := multSbtb;
    SModSem.mn := "Mult";
    SModSem.initial_mr := GRA.embed fblack;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SMult: SMod.t := {|
    SMod.get_modsem := fun _ => SMultSem;
    SMod.sk := [];
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Mult: Mod.t := (SMod.to_tgt GlobalStb) SMult.
End PROOF.

