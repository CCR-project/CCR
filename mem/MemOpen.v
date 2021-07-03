Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic.
Require Import Mem0 Mem1.
Require Import OpenDef.

Set Implicit Arguments.





Let _memRA: URA.t := (mblock ==> Z ==> (Excl.t val))%ra.





Section PROOF.
  Context `{@GRA.inG memRA Σ}.

  Definition alloc_spec: fspec :=
    (mk_simple (fun sz => (
                     (fun varg o => (⌜varg = [Vint (Z.of_nat sz)]↑ /\ (8 * (Z.of_nat sz) < modulus_64)%Z /\ o = ord_pure 0⌝)%I),
                     (fun vret => (∃ b, ⌜vret = (Vptr b 0)↑⌝ **
                                        OwnM ((b, 0%Z) |-> (List.repeat Vundef sz)))%I)
    ))).

  Definition free_spec: fspec :=
    (mk_simple (fun '(b, ofs) => (
                     (fun varg o => (∃ v, ⌜varg = ([Vptr b ofs])↑⌝ **
                                          OwnM ((b, ofs) |-> [v]) **
                                          ⌜o = ord_pure 0⌝)%I),
                     (fun vret => ⌜vret = (Vint 0)↑⌝%I)
    ))).

  Definition load_spec: fspec :=
    (mk_simple (fun '(b, ofs, v) => (
                     (fun varg o => ⌜varg = ([Vptr b ofs])↑⌝ **
                                    OwnM ((b, ofs) |-> [v]) **
                                    ⌜o = ord_pure 0⌝),
                     (fun vret => OwnM ((b, ofs) |-> [v]) ** ⌜vret = v↑⌝)
    ))).

  Definition store_spec: fspec :=
    (mk_simple
       (fun '(b, ofs, v_new) => (
            (fun varg o =>
               (∃ v_old, ⌜varg = ([Vptr b ofs ; v_new])↑⌝ **
                          OwnM ((b, ofs) |-> [v_old]) ** ⌜o = ord_pure 0⌝)%I),
            (fun vret => OwnM ((b, ofs) |-> [v_new]) ** ⌜vret = (Vint 0)↑⌝)
    ))).

  Definition cmp_spec: fspec :=
    (mk_simple
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
    [("alloc", mk_kspecbody alloc_spec (cfunU allocF) (fun _ => triggerNB));
    ("free",   mk_kspecbody free_spec  (cfunU freeF)  (fun _ => triggerNB));
    ("load",   mk_kspecbody load_spec  (cfunU loadF)  (fun _ => triggerNB));
    ("store",  mk_kspecbody store_spec (cfunU storeF) (fun _ => triggerNB));
    ("cmp",    mk_kspecbody cmp_spec   (cfunU cmpF)   (fun _ => triggerNB))
    ]
  .

  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun ksb => ksb.(ksb_fspec): fspec)) MemSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition KMemSem (sk: Sk.t): KModSem.t := {|
    KModSem.fnsems := MemSbtb;
    KModSem.mn := "Mem";
    KModSem.initial_mr := (GRA.embed (Auth.black (M:=_memRA) ε));
    KModSem.initial_st := (Mem.load_mem sk)↑;
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
