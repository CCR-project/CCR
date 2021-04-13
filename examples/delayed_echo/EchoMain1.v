Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Echo1.
Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

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

  Let main_spec: fspec := (mk_simple "Main" (X:=unit) (fun _ => ((fun _ o _ => o = ord_top), (top2)))).

  Definition MainStb: list (gname * fspec) :=
    [("main", main_spec)]
  .

  Definition MainSbtb: list (gname * fspecbody) :=
    [("main", mk_specbody main_spec main_body)]
  .

  Definition MainSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fsb) => (fn, fun_to_tgt (EchoStb ++ MainStb) fn fsb)) MainSbtb;
    ModSem.mn := "Main";
    ModSem.initial_mr := ε;
    ModSem.initial_st := ([]: list val)↑;
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.
