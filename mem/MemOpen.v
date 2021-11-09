Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import Mem0 Mem1.
Require Import OpenDef.

Set Implicit Arguments.





Let _memRA: URA.t := (mblock ==> Z ==> (Excl.t val))%ra.




Section TUNNEL.
  Context `{Σ: GRA.t}.
  Definition mk_tunneled {X: Type} (PQ: X -> ((Any.t -> ord -> iProp) * (Any.t -> iProp))): fspec :=
    (* mk_fspec (fun _ x y a o => (((fst ∘ PQ) x a o: iProp) ∧ ⌜y = tt↑⌝)%I) *)
    (*          (fun _ x z a => (((snd ∘ PQ) x a: iProp) ∧ ⌜z = tt↑⌝)%I) *)
    mk_fspec (fun _ x y a o =>
                match x with
                | Some x => (((fst ∘ PQ) x a o: iProp) ∧ ⌜y = tt↑⌝)%I
                | _ => ⌜y = a ∧ o = ord_top ∧ y <> tt↑⌝%I: iProp
                end)
             (fun _ x z a =>
                match x with
                | Some x => (((snd ∘ PQ) x a: iProp) (* ∧ ⌜z = tt↑⌝ *))%I
                | _ => ⌜z = a⌝%I: iProp
                end)
  .

  Context `{HasCallE: callE -< E}.
  Context `{HasEventE: eventE -< E}.
  Definition cfunU_tunneled {X Y} (body: X -> itree E Y): (option mname * Any.t) -> itree E Any.t :=
    fun '(_, varg) =>
      match varg↓ with
      | Some tt => triggerNB
      | _ => varg <- varg↓?;; vret <- body varg;; Ret vret↑
      end
  .

End TUNNEL.



Section PROOF.
  Context `{@GRA.inG memRA Σ}.

  Definition alloc_spec: fspec :=
    (mk_tunneled (fun sz => (
                     (fun varg o => (⌜varg = [Vint (Z.of_nat sz)]↑ /\ (8 * (Z.of_nat sz) < modulus_64)%Z /\ o = ord_pure 0⌝)%I),
                     (fun vret => (∃ b, ⌜vret = (Vptr b 0)↑⌝ **
                                        OwnM ((b, 0%Z) |-> (List.repeat Vundef sz)))%I)
    ))).

  Definition free_spec: fspec :=
    (mk_tunneled (fun '(b, ofs) => (
                     (fun varg o => (∃ v, ⌜varg = ([Vptr b ofs])↑⌝ **
                                          OwnM ((b, ofs) |-> [v]) **
                                          ⌜o = ord_pure 0⌝)%I),
                     (fun vret => ⌜vret = (Vint 0)↑⌝%I)
    ))).

  Definition load_spec: fspec :=
    (mk_tunneled (fun '(b, ofs, v) => (
                     (fun varg o => ⌜varg = ([Vptr b ofs])↑⌝ **
                                    OwnM ((b, ofs) |-> [v]) **
                                    ⌜o = ord_pure 0⌝),
                     (fun vret => OwnM ((b, ofs) |-> [v]) ** ⌜vret = v↑⌝)
    ))).

  Definition store_spec: fspec :=
    (mk_tunneled
       (fun '(b, ofs, v_new) => (
            (fun varg o =>
               (∃ v_old, ⌜varg = ([Vptr b ofs ; v_new])↑⌝ **
                          OwnM ((b, ofs) |-> [v_old]) ** ⌜o = ord_pure 0⌝)%I),
            (fun vret => OwnM ((b, ofs) |-> [v_new]) ** ⌜vret = (Vint 0)↑⌝)
    ))).

  Definition cmp_spec: fspec :=
    (mk_tunneled
       (fun '(result, resource) => (
          (fun varg o =>
          ((∃ b ofs v, ⌜varg = [Vptr b ofs; Vnullptr]↑⌝ ** ⌜resource = ((b, ofs) |-> [v])⌝ ** ⌜result = false⌝) ∨
           (∃ b ofs v, ⌜varg = [Vnullptr; Vptr b ofs]↑⌝ ** ⌜resource = ((b, ofs) |-> [v])⌝ ** ⌜result = false⌝) ∨
           (∃ b0 ofs0 v0 b1 ofs1 v1, ⌜varg = [Vptr b0 ofs0; Vptr b1 ofs1]↑⌝ **
                     ⌜resource = ((b0, ofs0) |-> [v0]) ⋅ ((b1, ofs1) |-> [v1])⌝ ** ⌜result = false⌝) ∨
           (∃ b ofs v, ⌜varg = [Vptr b ofs; Vptr b  ofs]↑⌝ ** ⌜resource = ((b, ofs) |-> [v])⌝ ** ⌜result = true⌝) ∨
           (⌜varg = [Vnullptr; Vnullptr]↑ /\ result = true⌝))
            ** OwnM(resource)
            ** ⌜o = ord_pure 0⌝
          ),
          (fun vret => OwnM(resource) ** ⌜vret = (if result then Vint 1 else Vint 0)↑⌝)
    ))).

End PROOF.



Section PROOF.
  Context `{@GRA.inG memRA Σ}.

  Definition MemSbtb: list (gname * kspecbody) :=
    [("alloc", mk_kspecbody alloc_spec (cfunU allocF) (cfunU_tunneled allocF));
    ("free",   mk_kspecbody free_spec  (cfunU freeF)  (cfunU_tunneled freeF));
    ("load",   mk_kspecbody load_spec  (cfunU loadF)  (cfunU_tunneled loadF));
    ("store",  mk_kspecbody store_spec (cfunU storeF) (cfunU_tunneled storeF));
    ("cmp",    mk_kspecbody cmp_spec   (cfunU cmpF)   (cfunU_tunneled cmpF))
    ]
  .

  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun ksb => ksb.(ksb_fspec): fspec)) MemSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Variable cslp cslr: gname -> bool.

  Definition KMemSem (sk: Sk.t): KModSem.t := {|
    KModSem.fnsems := MemSbtb;
    KModSem.mn := "Mem";
    KModSem.initial_mr := (GRA.embed (Auth.black (M:=_memRA) (initial_mem_mr cslr sk)));
    KModSem.initial_st := (Mem.load_mem cslp sk)↑;
  |}
  .
  Definition MemSem (stb: gname -> option fspec): Sk.t -> ModSem.t := (KModSem.transl_tgt stb) ∘ KMemSem.



  Definition KMem: KMod.t := {|
    KMod.get_modsem := KMemSem;
    KMod.sk := Sk.unit;
  |}
  .
  Definition Mem (stb: Sk.t -> gname -> option fspec): Mod.t := KMod.transl_tgt stb KMem.

End PROOF.
Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
