Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import Mem1.
Require Import AList.
Require Import MWHeader.

Set Implicit Arguments.



Definition _stkRA: URA.t := (mblock ==> (Excl.t (list val)))%ra.
Instance stkRA: URA.t := Auth.t _stkRA.

Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG mapRA Σ}.
  Context `{@GRA.inG memRA Σ}.

  Fixpoint is_map_internal (hd: val) (kvs: list (Z * Z)): iProp :=
    match kvs with
    | [] => (⌜hd = Vnullptr⌝: iProp)%I
    | (k,v) :: tl =>
      (∃ cur next, ⌜hd = Vptr cur 0⌝ ** (OwnM ((cur,0%Z) |-> [Vint k; Vint v; next])) **
                              is_map_internal next tl: iProp)%I
    end
  .

  (* Lemma unfold_is_map_internal: forall ll xs, *)
  (*     is_map_internal ll xs = *)
  (*     match xs with *)
  (*     | [] => (⌜ll = Vnullptr⌝: iProp)%I *)
  (*     | xhd :: xtl => *)
  (*       (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl])) *)
  (*                              ** is_map_internal ltl xtl: iProp)%I *)
  (*     end *)
  (* . *)
  (* Proof. *)
  (*   i. destruct xs; auto. *)
  (* Qed. *)

  (* Lemma unfold_is_map_internal_cons: forall ll xhd xtl, *)
  (*     is_map_internal ll (xhd :: xtl) = *)
  (*     (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl])) *)
  (*                            ** is_map_internal ltl xtl: iProp)%I. *)
  (* Proof. *)
  (*   i. eapply unfold_is_map_internal. *)
  (* Qed. *)


  Definition loop_spec: fspec :=
    mk_simple (fun '(h, k, v, kvs) =>
                 ((fun varg o => ⌜varg = ([Vptr h 0%Z; Vint k]: list val)↑ ∧ o = ord_pure 1 ∧
                                 alist_find k (kvs: list (Z * Z)) = Some v⌝ ** is_map_internal (Vptr h 0) kvs),
                  (fun vret => ⌜vret = (Vint v)↑⌝ ** (is_map_internal (Vptr h 0) kvs)))).

  Definition StackSbtb: list (gname * fspecbody) :=
    [("Map.new", mk_specbody new_spec (fun _ => triggerNB));
    ("Map.update", mk_specbody update_spec (fun _ => triggerNB));
    ("Map.access", mk_specbody access_spec (fun _ => triggerNB))
    ("Map.loop", mk_specbody loop_spec (fun _ => triggerNB))
    ]
  .

  Definition StackStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun ksb => ksb.(ksb_fspec): fspec)) StackSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition KStackSem: KModSem.t := {|
    KModSem.fnsems := StackSbtb;
    KModSem.mn := "Stack";
    KModSem.initial_mr := GRA.embed (@Auth.black _stkRA ε);
    KModSem.initial_st := (∅: gmap mblock (list val))↑;
  |}
  .
  Definition StackSem (stb: gname -> option fspec): ModSem.t :=
    KModSem.transl_tgt stb KStackSem.



  Definition KStack: KMod.t := {|
    KMod.get_modsem := fun _ => KStackSem;
    KMod.sk := [("new", Sk.Gfun); ("pop", Sk.Gfun); ("push", Sk.Gfun)];
  |}
  .
  Definition Stack (stb: Sk.t -> gname -> option fspec): Mod.t :=
    KMod.transl_tgt stb KStack.

End PROOF.
Global Hint Unfold StackStb: stb.
