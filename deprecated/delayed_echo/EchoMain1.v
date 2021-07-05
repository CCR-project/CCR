Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
Require Import Echo1.
(* Require Import TODOYJ. *)Logic.

Set Implicit Arguments.




Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.
  Context `{@GRA.inG Echo1.echoRA Σ}.

  Definition main_body: list val -> itree (hCallE +' pE +' eventE) val :=
    fun _ =>
      `n: val <- (hcall "echo" ([]: list val));;
      Ret Vundef
  .

  Let main_spec: fspec := (mk_simple (X:=unit) (fun _ => ((fun _ o => (⌜o = ord_top⌝: iProp)%I), (top2)))).

  Definition MainStb: list (gname * fspec) :=
    [("main", main_spec)]
  .

  Definition MainSbtb: list (gname * fspecbody) :=
    [("main", mk_specbody main_spec (cfun main_body))]
  .

  Definition SMain: SMod.t := SMod.main (fun _ o _ => o = ord_top) (cfun main_body).
  Definition Main: Mod.t := SMod.to_tgt (fun _ => to_stb MainStb) SMain.
  Definition SMainSem: SModSem.t := SModSem.main (fun _ o _ => o = ord_top) (cfun main_body).
  Definition MainSem: ModSem.t := SModSem.to_tgt (to_stb MainStb) SMainSem.

End PROOF.
