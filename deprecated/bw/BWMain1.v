Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
Require Import BW1.
(* Require Import TODOYJ. *)Logic.

Set Implicit Arguments.

Section MAIN.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG bwRA Σ}.

  Let getbool_spec:  fspec := (mk_simple (fun (_: unit) => ((fun _ o => (⌜True⌝: iProp)%I), (fun _ => (⌜True⌝: iProp)%I)))).

  Let putint_spec:  fspec := (mk_simple (fun (_: unit) => ((fun _ o => (⌜True⌝: iProp)%I), (fun _ => (⌜True⌝: iProp)%I)))).

  Definition ClientStb: list (gname * fspec) :=
    Seal.sealing "stb" [("getbool", getbool_spec) ; ("putint", putint_spec)].

  Let mainpre: Any.t -> ord -> Σ -> Prop := (fun varg o => (OwnM (bw_frag true) ** ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝)).
  Let main_spec: fspec := mk_simple (fun (_: unit) => (mainpre, fun _ => ⌜True⌝: iProp)%I).

  Definition mainbody: list val -> itree (hCallE +' pE +' eventE) val :=
    fun _ =>
      `b: val <- hcall "getbool" ([]: list val);; `b: bool <- (unbool b)?;;
      APC;;;
      `i: Z <- trigger (Choose _);;
      guarantee(i = if b then 0%Z else 0xffffff%Z);;;
      `_: val <- hcall "putint" [Vint i];;
      Ret Vundef
    .

  Definition MainStb: list (gname * fspec) :=
    Seal.sealing "stb" [("main", main_spec)].

  Definition MainSbtb: list (gname * fspecbody) :=
    [("main", mk_specbody main_spec (cfunN mainbody))
    ]
  .

  Definition SMain: SMod.t := SMod.main mainpre (cfunN mainbody).
  Definition Main: Mod.t := SMod.to_tgt (fun _ => to_stb (BWStb++ClientStb++MainStb)) SMain.
  Definition SMainSem: SModSem.t := SModSem.main mainpre (cfunN mainbody).
  Definition MainSem: ModSem.t := SModSem.to_tgt (to_stb (BWStb++ClientStb++MainStb)) SMainSem.

End MAIN.
Global Hint Unfold MainStb: stb.
Global Hint Unfold ClientStb: stb.
