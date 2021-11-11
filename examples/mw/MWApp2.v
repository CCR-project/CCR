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
  Context `{@GRA.inG spRA Σ}.

  Definition sbtb: list (string * fspecbody) :=
    [("App.init", mk_specbody init_spec (fun _ => `_: val <- ccallU "MW.put" [Vint 0; Vint 42];; Ret Vundef↑));
     ("App.run", mk_specbody run_spec (fun _ => `_: val <- ccallU "MW.get" [Vint 0];;
                                             syscallU "print" [42%Z];;; Ret Vundef↑))].

  Definition SAppSem: SModSem.t := {|
    SModSem.fnsems := sbtb;
    SModSem.mn := "App";
    SModSem.initial_mr := GRA.embed Run;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SApp: SMod.t := {|
    SMod.get_modsem := fun _ => SAppSem;
    SMod.sk := [("App.init", Sk.Gfun); ("App.run", Sk.Gfun); ("initialized", Sk.Gvar 0)];
  |}
  .

  Definition App (stb: Sk.t -> gname -> option fspec): Mod.t := (SMod.to_tgt stb) SApp.

End PROOF.
