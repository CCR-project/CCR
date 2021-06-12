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
Require Import TODO.
Require Import Mem0 Mem1.
Require Import OpenDef.

Set Implicit Arguments.





Let _memRA: URA.t := (mblock ==> Z ==> (Excl.t val))%ra.





Section PROOF.
  Context `{@GRA.inG memRA Σ}.

  Definition alloc_spec: fspec :=
    (mk_simple (fun sz => (
                     (fun varg o => (⌜varg = [Vint (Z.of_nat sz)]↑ /\ o = ord_pure 0⌝)%I),
                     (fun vret => (∃ b, ⌜vret = (Vptr b 0)↑⌝ **
                                        OwnM ((b, 0%Z) |-> (List.repeat (Vint 0) sz)))%I)
    ))).

  Definition free_spec: fspec :=
    (mk_simple (fun '(b, ofs) => (
                     (fun varg o => (∃ v, ⌜varg = ([Vptr b ofs])↑⌝ **
                                          OwnM ((b, ofs) |-> [v]) **
                                          ⌜o = ord_pure 0⌝)%I),
                     (fun _ => ⌜True⌝%I)
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
            (fun _ => OwnM ((b, ofs) |-> [v_new]))
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
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.

  Definition MemSbtb: list (gname * kspecbody) :=
    [("alloc", mk_kspecbody alloc_spec (cfun allocF) (fun _ => trigger (Choose _)));
    ("free",   mk_kspecbody free_spec  (cfun freeF)  (fun _ => trigger (Choose _)));
    ("load",   mk_kspecbody load_spec  (cfun loadF)  (fun _ => trigger (Choose _)));
    ("store",  mk_kspecbody store_spec (cfun storeF) (fun _ => trigger (Choose _)));
    ("cmp",    mk_kspecbody cmp_spec   (cfun cmpF)   (fun _ => trigger (Choose _)))
    ]
  .

  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun ksb => (KModSem.disclose_ksb ksb): fspec)) MemSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition KMemSem (sk: Sk.t): KModSem.t := {|
    KModSem.fnsems := MemSbtb;
    KModSem.mn := "Mem";
    KModSem.initial_mr := (GRA.embed (Auth.black (M:=_memRA) ε));
    KModSem.initial_st := (Sk.load_mem sk)↑;
  |}
  .
  Definition SMemSem: Sk.t -> SModSem.t := KMemSem.
  Definition MemSem (stb: list (gname * fspec)): Sk.t -> ModSem.t := (SModSem.to_tgt stb) ∘ SMemSem.



  Definition KMem: KMod.t := {|
    KMod.get_modsem := KMemSem;
    KMod.sk := Sk.unit;
  |}
  .
  Definition SMem: SMod.t := KMem.
  Definition Mem (stb: Sk.t -> list (gname * fspec)): Mod.t := SMod.to_tgt stb SMem.

End PROOF.
Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
