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

  Definition echo_body: list val -> itree (kCallE +' pE +' eventE) val :=
    fun args =>
      _ <- (pargs [] args)?;;
      APCK;;;
      `stk0: list Z    <- (kcall impure "input" ([]: list Z));;
      `_: list Z    <- (kcall impure "output" (stk0));;
      Ret Vundef
  .




  Let is_int_stack (h: mblock) (stk0: list Z): iProp :=
    (OwnM (is_stack h (List.map Vint stk0)) ∧ ⌜Forall (fun z => z <> (- 1)%Z) stk0⌝)%I
  .

  Definition input_spec: fspec :=
    mk_fspec (fun _ h _argh _argl o =>
                (∃ (stk0: list Z) (argl: list val),
                  ⌜_argh = stk0↑ ∧ _argl = argl↑ ∧ argl = [Vptr h 0] ∧ o = ord_top⌝
                   ** (is_int_stack h stk0))%I)
             (fun _ h _reth _retl => (∃ (stk1: list Z), ⌜_reth = stk1↑ ∧ _retl = Vundef↑⌝ ** is_int_stack h stk1)%I)
  .

  Definition input_body: list Z -> itree (kCallE +' pE +' eventE) (list Z) :=
    fun stk =>
      n <- (kcall impure "getint" ([]: list val));;
      n <- (parg Tint n)?;;
      if (dec n (- 1)%Z)
      then Ret stk
      else
        APCK;;;
        (kcall impure "input" (n :: stk))
  .





  Definition output_spec: fspec :=
    mk_fspec (fun _ h _argh _argl o =>
                (∃ (stk0: list Z) (argl: list val),
                  ⌜_argh = stk0↑ ∧ _argl = argl↑ ∧ argl = [Vptr h 0] ∧ o = ord_top⌝
                   ** is_int_stack h stk0)%I)
             (fun _ h _reth _retl => (∃ (stk1: list Z), ⌜_reth = stk1↑ ∧ _retl = Vundef↑⌝ ** is_int_stack h stk1)%I)
  .

  Definition output_body: list Z -> itree (kCallE +' pE +' eventE) (list Z) :=
    fun stk =>
      APCK;;;
      match stk with
      | [] => Ret []
      | n :: stk' => `_: val <- (kcall impure "putint" ([Vint n]: list val));; (kcall impure "output" (stk'))
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
    let x := constr:(List.map (map_snd (fun ksb => (KModSem.disclose_ksb_tgt ksb): fspec)) EchoSbtb) in
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
  Definition SEchoSem: SModSem.t := KEchoSem.
  Definition EchoSem (stb: gname -> option fspec): ModSem.t :=
    (SModSem.to_tgt stb) SEchoSem.



  Definition KEcho: KMod.t := {|
    KMod.get_modsem := fun _ => KEchoSem;
    KMod.sk := Sk.unit;
  |}
  .
  Definition SEcho: SMod.t := KEcho.
  Definition Echo (stb: Sk.t -> gname -> option fspec): Mod.t :=
    SMod.to_tgt stb SEcho.

End PROOF.
Global Hint Unfold EchoStb: stb.
