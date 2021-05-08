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

  Definition mainBody: list val -> itree (hCallE +' pE +' eventE) val :=
    fun _ =>
      APC;;;
      trigger (hCall false "unknown_call" ([]: list val, false)↑);;;
      APC;;;
      Ret (Vint 42)
  .

  Definition main_spec: fspec := mk_simple (fun (_: unit) => ((fun _ o => (⌜o = ord_top⌝: iProp)%I), top2)).

  Definition MainStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("main", main_spec)].
  Defined.

  Definition MainSbtb: list (gname * fspecbody) := [("main", mk_specbody main_spec mainBody)].

  Definition UnknownStb: list (gname * fspec) := [("unknown_call", fspec_trivial2)].

  Definition SMain: SMod.t := SMod.main (fun _ o _ => o = ord_top) mainBody.
  Definition Main: Mod.t := SMod.to_tgt (fun _ => MainStb ++ (List.map (map_snd disclose) MemStb) ++ UnknownStb) SMain.
  Definition SMainSem: SModSem.t := SModSem.main (fun _ o _ => o = ord_top) mainBody.
  Definition MainSem: ModSem.t := SModSem.to_tgt (MainStb ++ (List.map (map_snd disclose) MemStb) ++ UnknownStb) SMainSem.

End PROOF.
Global Hint Unfold MainStb: stb.
