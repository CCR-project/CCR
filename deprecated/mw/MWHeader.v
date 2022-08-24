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
| init
| run
| full
| boom
| unit
.

Let add := fun a0 a1 => match a0, a1 with
                                    | init, run => full
                                    | run, init => full
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
  core := fun _ => unit;
}
.
Next Obligation. subst add wf. i. destruct a, b; ss; des_ifs; ss. Qed.
Next Obligation. subst add wf. i. destruct a, b; ss; des_ifs; ss. Qed.
Next Obligation. subst add wf. i. unseal "ra". des_ifs. Qed.
Next Obligation. subst add wf. i. unseal "ra". ss. Qed.
Next Obligation. subst add wf. i. unseal "ra". des_ifs. Qed.
Next Obligation. subst add wf. i. unseal "ra". des_ifs. Qed.
Next Obligation. subst add wf. i. unseal "ra". des_ifs. Qed.
Next Obligation.
  i. exists unit. subst add. unseal "ra". des_ifs.
Qed.

End AppRA.
End AppRA.

Definition Init: AppRA.t := AppRA.init.
Definition Run: AppRA.t := AppRA.run.
Lemma _init_false: ~ URA.wf (Init ⋅ Init).
Proof.
  ii. rr in H. ur in H. rewrite Seal.sealing_eq in *. ss.
Qed.

Lemma _run_false: ~ URA.wf (Run ⋅ Run).
Proof.
  ii. rr in H. ur in H. rewrite Seal.sealing_eq in *. ss.
Qed.

Section PROOF.
  Context `{@GRA.inG AppRA.t Σ}.
  Lemma init_false: (OwnM Init ** OwnM Init ⊢ ⌜False⌝)%I.
  Proof.
    i. iIntros "[A B]". iCombine "A B" as "A". iOwnWf "A". exfalso. eapply _init_false; et.
  Qed.
  Lemma run_false: (OwnM Run ** OwnM Run ⊢ ⌜False⌝)%I.
  Proof.
    i. iIntros "[A B]". iCombine "A B" as "A". iOwnWf "A". exfalso. eapply _run_false; et.
  Qed.
End PROOF.


(*** simpl RA ***)
Instance spRA: URA.t := Auth.t (Excl.t unit).
Definition sp_white: spRA := @Auth.white (Excl.t unit) (Some tt).
Definition sp_black: spRA := @Auth.black (Excl.t unit) (Some tt).
Lemma _sp_white_false: ~ URA.wf (sp_white ⋅ sp_white).
Proof.
  ii. rr in H. ur in H. rewrite Seal.sealing_eq in *.
  rr in H. ur in H. rewrite Seal.sealing_eq in *. rr in H. ss.
Qed.

Lemma _sp_black_false: ~ URA.wf (sp_black ⋅ sp_black).
Proof.
  ii. rr in H. ur in H. rewrite Seal.sealing_eq in *. ss.
Qed.

Section PROOF.
  Context `{@GRA.inG spRA Σ}.
  Lemma sp_white_false: (OwnM (sp_white) ** OwnM (sp_white) ⊢ ⌜False⌝)%I.
  Proof.
    i. iIntros "[A B]". iCombine "A B" as "A". iOwnWf "A". exfalso. eapply _sp_white_false; et.
  Qed.
  Lemma sp_black_false: (OwnM (sp_black) ** OwnM (sp_black) ⊢ ⌜False⌝)%I.
  Proof.
    i. iIntros "[A B]". iCombine "A B" as "A". iOwnWf "A". exfalso. eapply _sp_black_false; et.
  Qed.
End PROOF.


(*** MW RA ***)
(* Instance _mwRA: URA.t := (Z ==> (Excl.t Z))%ra. *)
Instance _mwRA: URA.t := Excl.t (Z -> option Z)%ra.
Instance mwRA: URA.t := Auth.t _mwRA%ra.
Definition mw_state (f: Z -> option Z): mwRA := @Auth.white _mwRA (Some f).
Definition mw_stateX (f: Z -> option Z): mwRA := @Auth.black _mwRA (Some f).

Lemma _mw_state_false: forall f g, ~ URA.wf (mw_state f ⋅ mw_state g).
Proof.
  ii. rr in H. ur in H. rewrite Seal.sealing_eq in *.
  rr in H. ur in H. rewrite Seal.sealing_eq in *. rr in H. ss.
Qed.

Lemma _mw_stateX_false: forall f g, ~ URA.wf (mw_stateX f ⋅ mw_stateX g).
Proof.
  ii. rr in H. ur in H. rewrite Seal.sealing_eq in *. ss.
Qed.

Lemma _mw_state_eq: forall f g, URA.wf (mw_state f ⋅ mw_stateX g) -> f = g.
Proof.
  ii. rr in H. ur in H. rewrite Seal.sealing_eq in *. des. rr in H. des. ur in H. des_ifs.
Qed.

Lemma _mw_state_upd: forall f g h, URA.updatable (mw_state f ⋅ mw_stateX g) (mw_state h ⋅ mw_stateX h).
Proof.
  ii. rr in H. ur in H. rewrite Seal.sealing_eq in *. des_ifs.
  rr. ur. rewrite Seal.sealing_eq in *. des; ss. rr in H. ur in H. des. des_ifs.
  esplits; ss.
  { rr. esplits; et. ur. instantiate (1:=Excl.unit). ss. }
  { ur. ss. }
Qed.

Section PROOF.
  Context `{@GRA.inG mwRA Σ}.
  Lemma mw_state_false: forall f g, (OwnM (mw_state f) ⊢ OwnM (mw_state g) -* ⌜False⌝)%I.
  Proof.
    i. iIntros "A B". iCombine "A B" as "A". iOwnWf "A". exfalso. eapply _mw_state_false; et.
  Qed.
  Lemma mw_stateX_false: forall f g, (OwnM (mw_stateX f) ⊢ OwnM (mw_stateX g) -* ⌜False⌝)%I.
  Proof.
    i. iIntros "A B". iCombine "A B" as "A". iOwnWf "A". exfalso. eapply _mw_stateX_false; et.
  Qed.
  Lemma mw_state_eq: forall f g, (OwnM (mw_state f) ⊢ OwnM (mw_stateX g) -* ⌜f = g⌝)%I.
  Proof.
    i. iIntros "A B". iCombine "A B" as "A". iOwnWf "A". iPureIntro. eapply _mw_state_eq; et.
  Qed.
  Lemma mw_state_upd: forall f g h, (OwnM (mw_state f) ⊢ OwnM (mw_stateX g) -* #=> (OwnM (mw_state h) ** OwnM (mw_stateX h)))%I.
  Proof.
    i. iIntros "A B". iCombine "A B" as "A". iPoseProof (OwnM_Upd with "A") as "B".
    { eapply _mw_state_upd; et. }
    iMod "B". iModIntro. iDestruct "B" as "[A B]". iFrame.
  Qed.
End PROOF.



(* Definition _mapRA: URA.t := (mblock ==> (Excl.t (list (Z * Z))))%ra. *)
(* Definition _mapRA: URA.t := (mblock ==> (Excl.t (Z -> option Z)))%ra. *)
(* Instance mapRA: URA.t := Auth.t _mapRA. *)

Section MAPRA.
  Context `{@GRA.inG memRA Σ}.
  Fixpoint is_map_internal (hd: val) (kvs: list (Z * Z)): iProp :=
    match kvs with
    | [] => (⌜hd = Vnullptr⌝: iProp)%I
    | (k,v) :: tl =>
      (∃ cur next, ⌜hd = Vptr cur 0⌝ ** (OwnM ((cur,0%Z) |-> [Vint k; Vint v; next])) **
                              is_map_internal next tl: iProp)%I
    end
  .
  Definition is_map (h: mblock) (map: (Z -> option Z)): iProp :=
    (∃ hd kvs, is_map_internal hd kvs ** OwnM ((h,0%Z) |-> [hd]) **
        ⌜map = (fun k => alist_find k kvs) ∧ (Forall intrange_64 (List.map fst kvs))⌝)%I
  .
  (* Definition _is_map (h: mblock) (map: (Z -> option Z)): _mapRA := *)
  (*   (fun _h => if (dec _h h) then Some map else ε) *)
  (* . *)
  (* Definition is_map (h: mblock) (map: (Z -> option Z)): mapRA := Auth.white (_is_map h map). *)
End MAPRA.
Global Opaque is_map.







Section PROOF.
  Context `{@GRA.inG AppRA.t Σ}.
  Context `{@GRA.inG mwRA Σ}.
  Context `{@GRA.inG spRA Σ}.

  (* Definition mk_simple_frame {X: Type} (PQ: X -> ((Any.t -> ord -> iProp) * (Any.t -> iProp))): fspec := *)
  (*   mk_simple (fun '(FRAME, x) => let '(P, Q) := (PQ x) in *)
  (*                                 (fun varg ord => FRAME ** P varg ord, fun vret => FRAME ** Q vret)) *)
  (* . *)

  (******************************* MW ****************************)
  Definition main_spec: fspec :=
    mk_simple (fun (_: unit) =>
                 (ord_top,
                  (fun varg => ⌜varg = ([]: list val)↑⌝ ** OwnM Init
                                   ** OwnM (mw_stateX Maps.empty) ** OwnM sp_white),
                  (fun vret => ⌜vret = Vundef↑⌝ ** OwnM Run ** OwnM sp_white))).

  Definition loop_spec: fspec :=
    mk_simple (fun f =>
                 (ord_top,
                  (fun varg => ⌜varg = ([]: list val)↑⌝ ** OwnM Run
                                  ** OwnM (mw_state f) ** OwnM sp_white ∧ ⌜f 0 = Some 42%Z⌝),
                  (fun vret => ⌜vret = Vundef↑⌝ ** OwnM Run ** OwnM (mw_state f) ** OwnM sp_white))).

  Definition put_spec: fspec :=
    mk_simple (fun '(f, k, v) =>
                 (ord_top,
                  (fun varg => ⌜varg = [Vint k; Vint v]↑ ∧ intrange_64 k ∧ intrange_64 v⌝ ** OwnM (mw_state f) ** OwnM sp_white),
                  (fun vret => ⌜vret = Vundef↑⌝ ** OwnM (mw_state (add k v f)) ** OwnM sp_white)))
  .

  Definition get_spec: fspec :=
    mk_simple (fun '(f, k, v) =>
                 (ord_top,
                  (fun varg => ⌜varg = [Vint k]↑ ∧ intrange_64 k ∧ f k = Some v⌝ ** OwnM (mw_state f) ** OwnM sp_white),
                  (fun vret => ⌜vret = (Vint v)↑⌝ ** OwnM (mw_state f) ** OwnM sp_white)))
  .

  Definition MWStb: alist gname fspec.
    eapply (Seal.sealing "stb").
    eapply [("main",main_spec); ("MW.loop",loop_spec); ("MW.put",put_spec); ("MW.get",get_spec)].
  Defined.




  (******************************* App ****************************)
  (* Definition init_spec0: fspec := *)
  (*   mk_simple (fun (_: unit) => ( *)
  (*                  (fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Init), *)
  (*                  (fun vret => ⌜vret = Vundef↑⌝ ** OwnM Run))). *)

  (* Definition run_spec0: fspec := *)
  (*   mk_simple (fun (_: unit) => ( *)
  (*                  (fun varg o => ⌜varg = ([]: list val)↑ ∧ o = ord_top⌝ ** OwnM Run), *)
  (*                  (fun vret => ⌜vret = Vundef↑⌝ ** OwnM Run))). *)

  Definition init_spec: fspec :=
    mk_simple (fun f => (ord_top,
                         (fun varg => ⌜varg = ([]: list val)↑⌝ ** OwnM Init ** OwnM (mw_state f) ** OwnM (sp_white)),
                         (fun vret => ⌜vret = Vundef↑⌝ ** OwnM Run ** OwnM (mw_state (add 0%Z 42%Z f)) ** OwnM (sp_white)))).

  Definition run_spec: fspec :=
    mk_simple (fun f => (ord_top,
                         (fun varg => ⌜varg = ([]: list val)↑⌝ ** OwnM Run ** OwnM (mw_state f) ** OwnM (sp_white) ∧ ⌜f 0 = Some 42%Z⌝),
                         (fun vret => ⌜vret = Vundef↑⌝ ** OwnM Run ** OwnM (mw_state f) ** OwnM (sp_white) ∧ ⌜f 0 = Some 42%Z⌝))).

  Definition AppStb: alist gname fspec.
    eapply (Seal.sealing "stb").
    eapply [("App.init",init_spec); ("App.run",run_spec)].
  Defined.



  (******************************* Map ****************************)
  Context `{@GRA.inG memRA Σ}.

  Definition new_spec: fspec :=
    (mk_simple (fun (_: unit) => (
                    ord_pure 2,
                    (fun varg => (⌜varg = ([]: list val)↑⌝: iProp)%I),
                    (fun vret => (∃ h, ⌜vret = (Vptr h 0)↑⌝ ** is_map h (fun _ => None): iProp)%I)
    )))
  .

  Definition update_spec: fspec :=
    mk_simple (fun '(h, k, v, m) =>
                 (ord_pure 2,
                  (fun varg => (⌜varg = ([Vptr h 0%Z; Vint k; Vint v]: list val)↑ ∧ intrange_64 k⌝ **
                                   is_map h m)%I),
                  (fun vret => ⌜vret = Vundef↑⌝ ** is_map h (Maps.add k v m)))).

  Definition access_spec: fspec :=
    mk_simple (fun '(h, k, v, m) =>
                 (ord_pure Ord.omega,
                  (fun varg => ⌜varg = ([Vptr h 0%Z; Vint k]: list val)↑ ∧ m k = Some v⌝ **
                                  is_map h m),
                  (fun vret => ⌜vret = (Vint v)↑⌝ ** (is_map h m)))).

  Definition access_loop_spec: fspec :=
    mk_simple (fun '(h, k, v, kvs) =>
                 (ord_pure (1 + length kvs)%ord,
                  (fun varg => ⌜varg = ([Vptr h 0%Z; Vint k]: list val)↑ ∧
                                 alist_find k (kvs: list (Z * Z)) = Some v ∧
                                 (Forall intrange_64 (List.map fst kvs))⌝
                                ** is_map_internal (Vptr h 0) kvs),
                  (fun vret => ⌜vret = (Vint v)↑⌝ ** (is_map_internal (Vptr h 0) kvs)))).

  Definition MapStb: alist gname fspec.
    eapply (Seal.sealing "stb").
    eapply [("Map.new",new_spec); ("Map.update",update_spec); ("Map.access",access_spec);
           ("Map.loop",access_loop_spec)].
  Defined.





  Definition fspec_mw1: fspec :=
    mk_fspec (meta:=unit) (fun _ => ord_top) (fun _ _ argh argl => (⌜argh = argl⌝ ** OwnM (sp_white))%I)
             (fun _ _ reth retl => (⌜reth = retl⌝ ** OwnM (sp_white))%I)
  .

  (******************************* Dedicated STB for MW1 ****************************)

  Definition MW1Stb: alist gname fspec.
    eapply (Seal.sealing "stb").
    eapply [("main", fspec_mw1); ("MW.loop", fspec_mw1); ("MW.put", fspec_mw1); ("MW.get", fspec_mw1);
            ("App.init", fspec_mw1); ("App.run", fspec_mw1);
            ("Map.new", fspec_trivial); ("Map.access", fspec_trivial); ("Map.update", fspec_trivial);
            ("alloc", alloc_spec); ("free", free_spec); ("load", load_spec); ("store", store_spec); ("cmp", cmp_spec)].
   Defined.

  (******************************* Dedicated STB for App1 ****************************)
  Definition init_spec1: fspec :=
    mk_simple (fun (_: unit) => (ord_top,
                                 (fun varg => OwnM Init),
                                 (fun vret => OwnM Run))).
  Definition run_spec1: fspec :=
    mk_simple (fun (_: unit) => (ord_top,
                                 (fun varg => OwnM Run),
                                 (fun vret => OwnM Run))).
  Definition App1Stb: alist gname fspec.
    eapply (Seal.sealing "stb").
    eapply [("MW.put", fspec_trivial); ("MW.get", fspec_trivial)].
   Defined.

End PROOF.
Global Hint Unfold MWStb MW1Stb AppStb App1Stb MapStb: stb.



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



(*** TODO: MOVE TO ImpPrelude ***)
Definition add_ofs (ptr: val) (d: Z): val :=
  match ptr with
  | Vptr b ofs => Vptr b (ofs + d)
  | _ => Vundef
  end
.

Lemma scale_int_8 n: scale_int (8 * n) = Some n.
Proof.
  unfold scale_int. des_ifs.
  - rewrite Z.mul_comm. rewrite Z.div_mul; ss.
  - contradict n0. eapply Z.divide_factor_l.
Qed.

(* Section PROOF. *)
(*   Context `{eventE -< E}. *)
(*   Definition syscallU (name: string) (vs: list Z): itree E Z := *)
(*     z <- trigger (Syscall name vs↑ top1);; `z: Z <- z↓?;; Ret z *)
(*   . *)
(* End PROOF. *)
Notation syscallU name vs := (z <- trigger (Syscall name vs↑ top1);; `z: Z <- z↓?;; Ret z).
