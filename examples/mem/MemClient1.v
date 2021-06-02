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
Require Import OpenDef Open.

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

  Definition KPC: itree (kCallE +' pE +' eventE) unit :=
    fn <- trigger (Choose _);; trigger (kCall fn (@inl unit (list val) tt));;; Ret tt
  .

  Definition clientBody: list val -> itree (kCallE +' pE +' eventE) val :=
    fun _ =>
      KPC;;;
      KPC;;;
      trigger (kCall "unknown_call" (@inr unit (list val) []));;;
      KPC;;;
      Ret (Vint 42)
  .

  Definition client_spec: ftspec unit unit :=
    mk_ksimple (fun (_: unit) => ((fun _ o => (⌜o = ord_top⌝)%I), (fun _ => ⌜True⌝%I)))
  .

  Definition ClientStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("client", mk_fspec client_spec)].
  Defined.

  Definition ClientSbtb: list (gname * kspecbody) :=
    [("client", mk_kspecbody client_spec clientBody)
    ]
  .

  Definition UnknownStb: list (gname * fspec) := [("unknown_call", fspec_trivial2)].

  Definition KClientSem: KModSem.t := {|
    KModSem.fnsems := ClientSbtb;
    KModSem.mn := "Client";
    KModSem.initial_mr := ε;
    KModSem.initial_st := tt↑;
  |}
  .

  Definition SClientSem: SModSem.t := (KModSem.to_tgt) KClientSem.

  Definition ClientSem: ModSem.t := (SModSem.to_tgt MemStb) SClientSem.

  Definition KClient: KMod.t := {|
    KMod.get_modsem := fun _ => KClientSem;
    KMod.sk := Sk.unit;
  |}
  .

  Definition SClient: SMod.t := (KMod.to_tgt) KClient.

  Definition Client: Mod.t := SMod.to_tgt (fun _ => MemStb) SClient.

End PROOF.
Global Hint Unfold ClientStb: stb.
