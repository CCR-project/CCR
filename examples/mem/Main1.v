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

  Definition mainBody: list val -> itree (kCallE +' pE +' eventE) val :=
    fun _ =>
      KPC;;;
      KPC;;;
      trigger (kCall "unknown_call" (@inr unit (list val) []));;;
      KPC;;;
      Ret (Vint 42)
  .

  Definition main_spec: ftspec unit unit :=
    mk_ksimple (fun (_: unit) => ((fun _ o => (⌜o = ord_top⌝)%I), (fun _ => ⌜True⌝%I)))
  .

  Definition MainStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("main", mk_fspec main_spec)].
  Defined.

  (* Definition MainSbtb: list (gname * fspecbody) := [("main", mk_specbody main_spec mainBody)]. *)

  Definition UnknownStb: list (gname * fspec) := [("unknown_call", fspec_trivial2)].

  TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT
  Definition KMainSem: KModSem.t := SModSem.main (fun _ o => (⌜o = ord_top⌝: iProp)%I) mainBody.
  Definition SMainSem: SModSem.t := SModSem.main (fun _ o => (⌜o = ord_top⌝: iProp)%I) mainBody.
  Definition MainSem: ModSem.t := SModSem.to_tgt MainStb SMainSem.
  Definition SMain: SMod.t := SMod.main (fun _ o => (⌜o = ord_top⌝: iProp)%I) mainBody.
  Definition Main: Mod.t := SMod.to_tgt (fun _ => MainStb) SMain.

End PROOF.
Global Hint Unfold MainStb: stb.
