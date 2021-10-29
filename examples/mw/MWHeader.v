Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import ProofMode.
Require Import Mem1.

Set Implicit Arguments.


Module AppRA.
Section AppRA.

Variant car: Type :=
| half (usable: bool)
| full
| boom
| unit
.

Let add := fun a0 a1 => match a0, a1 with
                                    | half true, half true => full
                                    | half false, half false => full
                                    | _, unit => a0
                                    | unit, _ => a1
                                    | _, _ => boom
                                    end.
Let wf := fun a => match a with | boom => False | _ => True end.

Program Instance t: URA.t := {
  car := car;
  unit := unit;
  _add := add;
  _wf := wf;
}
.
Next Obligation. subst add wf. i. destruct a, b; ss; des_ifs; ss. Qed.
Next Obligation. subst add wf. i. destruct a, b; ss; des_ifs; ss. Qed.
Next Obligation. subst add wf. i. unseal "ra". des_ifs. Qed.
Next Obligation. subst add wf. i. unseal "ra". ss. Qed.
Next Obligation. subst add wf. i. unseal "ra". des_ifs. Qed.

End AppRA.
End AppRA.

Definition Init: AppRA.t := AppRA.half false.
Definition InitX: AppRA.t := AppRA.half false.
Definition Run: AppRA.t := AppRA.half true.
Definition RunX: AppRA.t := AppRA.half true.



Instance _mwRA: URA.t := (Z ==> (Excl.t Z))%ra.
Instance mwRA: URA.t := Auth.t _mwRA%ra.
Definition mw_state (f: Z -> option Z): mwRA := @Auth.white _mwRA f.
Definition mw_stateX (f: Z -> option Z): mwRA := @Auth.black _mwRA f.




Definition _mapRA: URA.t := (mblock ==> (Excl.t (list (Z * Z))))%ra.
Instance mapRA: URA.t := Auth.t _mapRA.
Definition _is_map (h: mblock) (map: list (Z * Z)): _mapRA :=
  (fun _h => if (dec _h h) then Some map else ε)
.
Definition is_map (h: mblock) (map: list (Z * Z)): mapRA := Auth.white (_is_map h map).







Section PROOF.
  Context `{@GRA.inG AppRA.t Σ}.
  Context `{@GRA.inG mwRA Σ}.

  Definition mk_simple_frame {X: Type} (PQ: X -> ((Any.t -> ord -> iProp) * (Any.t -> iProp))): fspec :=
    mk_simple (fun '(FRAME, x) => let '(P, Q) := (PQ x) in
                                  (fun varg ord => FRAME ** P varg ord, fun vret => FRAME ** Q vret))
  .

  Definition init_spec0: fspec :=
    mk_simple (fun (_: unit) => (
                   (fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Init),
                   (fun vret => ⌜vret = Vundef↑⌝ ** OwnM Run))).

  Definition run_spec0: fspec :=
    mk_simple (fun (_: unit) => (
                   (fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Run),
                   (fun vret => ⌜vret = Vundef↑⌝ ** OwnM Run))).

  Definition main_spec: fspec :=
    mk_simple (fun (_: unit) =>
                 ((fun varg o => OwnM Init),
                  (fun vret => OwnM Run))).

  Definition put_spec: fspec :=
    mk_simple (fun '(f, k, v) =>
                 ((fun varg o => ⌜varg = [Vint k; Vint v]↑ ∧ intrange_64 k ∧ intrange_64 v⌝ ** OwnM (mw_state f)),
                  (fun vret => OwnM (mw_state (add k v f)))))
  .

  Definition get_spec: fspec :=
    mk_simple (fun '(f, k, v) =>
                 ((fun varg o => ⌜varg = [Vint k]↑ ∧ intrange_64 k ∧ f k = Some v⌝ ** OwnM (mw_state f)),
                  (fun vret => ⌜vret = (Vint v)↑⌝ ** OwnM (mw_state f))))
  .

  Definition init_spec1: fspec :=
    mk_simple (fun f => ((fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Init ** OwnM (mw_state f)),
                         (fun vret => OwnM Run ** OwnM (mw_state (add 0%Z 42%Z f))))).

  Definition run_spec1: fspec :=
    mk_simple (fun f => ((fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Run ** OwnM (mw_state f) ∧ ⌜f 0 = Some 42%Z⌝),
                         (fun vret => OwnM Run ** OwnM (mw_state f) ∧ ⌜f 0 = Some 42%Z⌝))).

  Definition GlobalStb0: gname -> option fspec :=
    to_stb [("init",init_spec0); ("run",run_spec0); ("main",fspec_trivial); ("put",fspec_trivial); ("get",fspec_trivial)].

  Definition GlobalStb1: gname -> option fspec :=
    to_stb [("init",init_spec1); ("run",run_spec1); ("main",main_spec); ("put",put_spec); ("get",get_spec)].

  Context `{@GRA.inG memRA Σ}.

  Definition GlobalStbC: list (gname * fspec).
    eapply (Seal.sealing "stb").
    eapply [("main", fspec_trivial); ("loop", fspec_trivial); ("put", fspec_trivial); ("get", fspec_trivial);
            ("init", fspec_trivial); ("run", fspec_trivial);
            ("new", fspec_trivial); ("access", fspec_trivial); ("update", fspec_trivial);
            ("alloc", alloc_spec); ("free", free_spec); ("load", load_spec); ("store", store_spec); ("cmp", cmp_spec)].
    (* set (x:=(List.map (fun x => (x, fspec_trivial)) ["main"; "loop"; "put"; "get"; "init"; "run"; "access"; "update"] ++ *)
    (*                   [("alloc", alloc_spec); ("free", free_spec); ("load", load_spec); ("store", store_spec); ("cmp", cmp_spec)])). *)
    (* unfold map in x. *)
    (* exact x. *)
  Defined.
  (* Definition GlobalStbC: gname -> option fspec := *)
  (*   to_stb (List.map (fun x => (x, fspec_trivial)) ["main"; "loop"; "put"; "get"; "init"; "run"; "access"; "update"] ++ MemStb) *)
  (* . *)

End PROOF.
Global Hint Unfold GlobalStb0: stb.
Global Hint Unfold GlobalStb1: stb.
Global Hint Unfold GlobalStbC: stb.



Definition set `{Dec K} V (k: K) (v: V) (f: K -> V): K -> V := fun k0 => if dec k k0 then v else f k0.



Section PROOF.
  Context `{Σ: GRA.t}.
  
  Lemma Own_unit
    :
      bi_entails True%I (Own ε)
  .
  Proof.
    red. uipropall. ii. rr. esplits; et. rewrite URA.unit_idl. refl.
  Qed.

  Context `{@GRA.inG M Σ}.

  Lemma embed_unit
    :
      (GRA.embed ε) = ε
  .
  Proof.
    unfold GRA.embed.
    Local Transparent GRA.to_URA. unfold GRA.to_URA. Local Opaque GRA.to_URA.
    Local Transparent URA.unit. unfold URA.unit. Local Opaque URA.unit.
    cbn.
    apply func_ext_dep. i.
    dependent destruction H. ss. rewrite inG_prf. cbn. des_ifs.
  Qed.

End PROOF.

Section PROOF.
  Context `{@GRA.inG M Σ}.

  Lemma OwnM_unit
    :
      bi_entails True%I (OwnM ε)
  .
  Proof.
    unfold OwnM. r. uipropall. ii. rr. esplits; et. rewrite embed_unit. rewrite URA.unit_idl. refl.
  Qed.
End PROOF.

