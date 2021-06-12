Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Logic.
Require Import TODOYJ.
Require Import OpenDef.

Set Implicit Arguments.



Require Import Mem1 MemOpen.


(* Notation "'hCall2' fn varg" := *)
(*   (marg <- trigger (Choose _);; vret <- trigger (hCall fn marg varg);; vret <- vret↓?;; Ret vret) *)
(*     (at level 60). *)
(* Definition hCall' {X} (fn: string) (varg: Any.t): itree (hCallE +' eventE) X := *)
(*   marg <- trigger (Choose _);; vret <- trigger (hCall fn marg varg);; vret <- vret↓?;; Ret vret *)
(* . *)
  (* marg <- trigger (Choose _);; trigger (hCall fn marg varg) >>= ((?) <*> (↓)) *)

Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  (***
        void* x = malloc(1);
        *x = 42;
        unknown_call(); // may GUESS the location &x and change the contents
        y = *x;
        return y; ~~~> return 42;
   ***)

  Definition clientBody: list val -> itree (kCallE +' pE +' eventE) val :=
    fun _ =>
      APCK;;;
      trigger (kCall false false "unknown_call" (([]: list val)↑));;;
      APCK;;;
      Ret (Vint 42)
  .

  Definition client_spec: fspec :=
    mk_simple (fun (_: unit) => ((fun _ o => (⌜o = ord_top⌝)%I), (fun _ => ⌜True⌝%I)))
  .

  Definition ClientSbtb: list (gname * kspecbody) :=
    [("client", mk_kspecbody client_spec (cfun clientBody) (cfun clientBody))
    ]
  .

  Definition ClientStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun ksb => (KModSem.disclose_ksb ksb): fspec)) ClientSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition UnknownStb: list (gname * fspec).
   eapply (Seal.sealing "stb").
   eapply [("unknown_call", fspec_trivial)].
  Defined.

  Definition KClientSem: KModSem.t := {|
    KModSem.fnsems := ClientSbtb;
    KModSem.mn := "Client";
    KModSem.initial_mr := ε;
    KModSem.initial_st := tt↑;
  |}
  .

  Definition SClientSem: SModSem.t := (KModSem.to_tgt) KClientSem.

  Definition ClientSem (stb: list (string * fspec)): ModSem.t :=
    (SModSem.to_tgt stb) SClientSem.

  Definition KClient: KMod.t := {|
    KMod.get_modsem := fun _ => KClientSem;
    KMod.sk := Sk.unit;
  |}
  .

  Definition SClient: SMod.t := (KMod.to_tgt) KClient.

  Definition Client (stb: Sk.t -> list (string * fspec)): Mod.t :=
    SMod.to_tgt stb SClient.

End PROOF.
Global Hint Unfold ClientStb: stb.
Global Hint Unfold UnknownStb: stb.
