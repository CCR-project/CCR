Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Mem1 MemOpen.
Require Import TODOYJ.
Require Import NewEchoHeader.
Require Import IPM HoareDef OpenDef.
Require Import NewStack3A.

Set Implicit Arguments.




Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Definition echo_body: list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      trigger hAPC;;;
      `stk0: list Z    <- (ccallN "input" ([]: list Z));;
      `_: list Z    <- (ccallN "output" (stk0));;
      Ret Vundef
  .




  Let is_int_stack (h: mblock) (stk0: list Z): iProp :=
    (OwnM (is_stack h (List.map Vint stk0)) ∧ ⌜Forall (fun z => (z <> (- 1)%Z) /\ (intrange_64 z)) stk0⌝)%I
  .

  Definition input_spec: fspec :=
    mk_fspec (fun _ h _argh _argl o =>
                (∃ (stk0: list Z) (argl: list val),
                  ⌜_argh = stk0↑ ∧ _argl = argl↑ ∧ argl = [Vptr h 0] ∧ o = ord_top⌝
                   ** (is_int_stack h stk0))%I)
             (fun _ h _reth _retl => (∃ (stk1: list Z), ⌜_reth = stk1↑ ∧ _retl = Vundef↑⌝ ** is_int_stack h stk1)%I)
  .

  Definition input_body: list Z -> itree hEs (list Z) :=
    fun stk =>
      n <- (ccallU "getint" ([]: list val));;
      assume (wf_val n);;;
      n <- (parg Tint n)?;;
      if (dec n (- 1)%Z)
      then Ret stk
      else
        trigger hAPC;;;
        (ccallN "input" (n :: stk))
  .





  Definition output_spec: fspec :=
    mk_fspec (fun _ h _argh _argl o =>
                (∃ (stk0: list Z) (argl: list val),
                  ⌜_argh = stk0↑ ∧ _argl = argl↑ ∧ argl = [Vptr h 0] ∧ o = ord_top⌝
                   ** is_int_stack h stk0)%I)
             (fun _ h _reth _retl => (∃ (stk1: list Z), ⌜_reth = stk1↑ ∧ _retl = Vundef↑⌝ ** is_int_stack h stk1)%I)
  .

  Definition output_body: list Z -> itree hEs (list Z) :=
    fun stk =>
      trigger hAPC;;;
      match stk with
      | [] => Ret []
      | n :: stk' => `_: val <- (ccallU "putint" ([Vint n]: list val));; (ccallN "output" (stk'))
      end
  .





  Definition EchoSbtb: list (gname * kspecbody) :=
    [("echo", ksb_trivial (cfunU echo_body));
    ("input",  mk_kspecbody input_spec (fun _ => triggerUB) (cfunN input_body));
    ("output", mk_kspecbody output_spec (fun _ => triggerUB) (cfunN output_body))
    ]
  .

  Definition EchoStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun ksb => ksb.(ksb_fspec): fspec)) EchoSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition KEchoSem: KModSem.t := {|
    KModSem.fnsems := EchoSbtb;
    KModSem.mn := "Echo";
    KModSem.initial_mr := ε;
    KModSem.initial_st := (∅: gmap mblock (list Z))↑;
  |}
  .
  Definition EchoSem (stb: gname -> option fspec): ModSem.t :=
    KModSem.transl_tgt stb KEchoSem.



  Definition KEcho: KMod.t := {|
    KMod.get_modsem := fun _ => KEchoSem;
    KMod.sk := Sk.unit;
  |}
  .
  Definition Echo (stb: Sk.t -> gname -> option fspec): Mod.t :=
    KMod.transl_tgt stb KEcho.

End PROOF.
Global Hint Unfold EchoStb: stb.
