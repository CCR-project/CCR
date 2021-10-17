Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import MWHeader.
Require Import STB.

Set Implicit Arguments.



Section PROOF.

  Context `{@GRA.inG AppRA.t Σ}.
  Context `{@GRA.inG mwRA Σ}.

  Definition sbtb: list (string * fspecbody) :=
    [("init", mk_specbody init_spec1 (fun _ => `_: val <- ccallU "put" [Vint 0; Vint 42];; Ret Vundef↑));
     ("run", mk_specbody run_spec1 (fun _ => `_: val <- ccallU "get" [Vint 0];;
                                             trigger (Syscall "print" [Vint 42]↑ top1);;; Ret Vundef↑))].

  Definition SAppSem: SModSem.t := {|
    SModSem.fnsems := sbtb;
    SModSem.mn := "App";
    SModSem.initial_mr := GRA.embed InitX;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SApp: SMod.t := {|
    SMod.get_modsem := fun _ => SAppSem;
    SMod.sk := [("init", Sk.Gfun); ("run", Sk.Gfun)];
  |}
  .

  Definition App: Mod.t := (SMod.to_tgt (fun _ => GlobalStb1)) SApp.

End PROOF.
