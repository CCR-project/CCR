Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Stack1 Client1 Mem1.
Require Import TODOYJ.
Require Import Logic.

Set Implicit Arguments.




Section PROOF.

  Context {Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  Definition is_minus_one (v: val): bool :=
    match v with
    | Vint i => dec i (- 1)%Z
    | _ => false
    end
  .

  Definition echo_body: list Z -> itree (hCallE +' pE +' eventE) unit :=
    fun ns =>
      n <- trigger (hCall false "getint" ([]: list val)↑);;
      `n: val <- n↓?;; `n: Z <- (unint n)?;;
      if dec n (- 1)%Z
      then trigger (hCall false "echo_finish" ns↑);;; Ret tt
      else
        trigger (hCall false "echo" (n :: ns)↑);;;
        Ret tt
  .

  Definition echo_finish_body: list Z -> itree (hCallE +' pE +' eventE) unit :=
    fun ns =>
      match ns with
      | [] => Ret tt
      | hd :: tl =>
        trigger (hCall false "putint" [Vint hd]↑);;;
        trigger (hCall false "echo_finish" tl↑);;;
        Ret tt
      end
  .

  Let echo_spec:        fspec := (@mk _ (list Z) (list Z) unit (top5) (top4)).
  Let echo_finish_spec: fspec := (@mk _ (list Z) (list Z) unit (top5) (top4)).

  Definition EchoStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("echo", echo_spec) ; ("echo_finish", echo_finish_spec)].
  Defined.

  Definition EchoSbtb: list (gname * fspecbody) :=
    [("echo", mk_specbody echo_spec (cfun echo_body)); ("echo_finish", mk_specbody echo_finish_spec (cfun echo_finish_body))]
  .

  Definition SEchoSem: SModSem.t := {|
    SModSem.fnsems := EchoSbtb;
    SModSem.mn := "Echo";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition EchoSem: ModSem.t := (SModSem.to_tgt (StackStb ++ ClientStb ++ MemStb ++ EchoStb)) SEchoSem.

  Definition SEcho: SMod.t := {|
    SMod.get_modsem := fun _ => SEchoSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition Echo: Mod.t := (SMod.to_tgt (fun _ => MemStb ++ StackStb)) SEcho.

End PROOF.
Global Hint Unfold EchoStb: stb.
