Require Import Coqlib.
Require Import Universe.
Require Import PCM.

Set Implicit Arguments.



Fixpoint _find_idx {A} (f: A -> bool) (l: list A) (acc: nat): option (nat * A) :=
  match l with
  | [] => None
  | hd :: tl => if (f hd) then Some (acc, hd) else _find_idx f tl (S acc)
  end
.

Definition find_idx {A} (f: A -> bool) (l: list A): option (nat * A) := _find_idx f l 0.

Notation "'do' ' X <- A ; B" := (o_bind A (fun _x => match _x with | X => B end))
                                  (at level 200, X pattern, A at level 100, B at level 200)
                                : o_monad_scope.


Module SkEnv.

  Record t: Type := mk {
    blk2id: block -> option gname;
    id2blk: gname -> option block;
  }
  .

  Definition wf (ske: t): Prop :=
    forall id blk, ske.(id2blk) id = Some blk <-> ske.(blk2id) blk = Some id.

  (* Definition project: t -> Sk.t -> t := admit "". *)
    (* t: Type := Genv.t (fundef signature) unit; *)
    (* wf: t -> Prop; *)
    (* wf_mem: t -> Sk.t -> mem -> Prop; *)
    (* to_senv: t -> Senv.t := Genv.to_senv; *)
    (* project: t -> Sk.t -> t; *)
    (* project_spec: t -> Sk.t -> t -> Prop; *)
    (* includes: t -> Sk.t -> Prop; *)
    (* project_impl_spec: forall skenv sk (INCL: includes skenv sk), *)
    (*     (<<PROJ: project_spec skenv sk (project skenv sk)>>); *)
    (* linkorder_includes: forall *)
    (*     (sk0 sk1: Sk.t) *)
    (*     (LO: linkorder sk0 sk1) *)
    (*   , *)
    (*     (<<INCL: includes (Sk.load_skenv sk1) sk0>>); *)
    (* empty: t; *)
    (* load_skenv_wf: forall *)
    (*     sk *)
    (*     (WF: Sk.wf sk) *)
    (*   , *)
    (*     (<<WF: wf (Sk.load_skenv sk)>>) *)
    (* ; *)
    (* load_skenv_wf_mem: forall *)
    (*     sk_link m_init *)
    (*     (WF: Sk.wf sk_link) *)
    (*     (LOADM: Sk.load_mem sk_link = Some m_init) *)
    (*   , *)
    (*     let skenv_link := Sk.load_skenv sk_link in *)
    (*     <<WFM: forall sk (WF: Sk.wf sk) (LO: linkorder sk sk_link), wf_mem skenv_link sk m_init>> *)
    (* ; *)
    (* disj (ske0 ske1: t): Prop := forall *)
    (*   fptr f0 f1 *)
    (*   (FINDF: Genv.find_funct ske0 fptr = Some (Internal f0)) *)
    (*   (FINDF: Genv.find_funct ske1 fptr = Some (Internal f1)) *)
    (* , *)
    (*   False; *)
    (* project_respects_disj: forall *)
    (*     sk0 sk1 ske0 ske1 ske_link *)
    (*     (DISJ: Sk.disj sk0 sk1) *)
    (*     (LOAD0: project ske_link sk0 = ske0) *)
    (*     (LOAD1: project ske_link sk1 = ske1) *)
    (*   , *)
    (*     (<<DISJ: disj ske0 ske1>>) *)
    (* ; *)
    (* project_linkorder: forall *)
    (*     skenv_link fptr sk ef fd *)
    (*     (FINDF0: Genv.find_funct skenv_link fptr = Some (External ef)) *)
    (*     (FINDF1: Genv.find_funct (project skenv_link sk) fptr = Some (Internal fd)) *)
    (*   , *)
    (*     False *)
    (* ; *)

End SkEnv.






(* Require Import Logic.FinFun. *)
(* Definition finfun A B: Type := *)
(*   { f: A -> option B | *)
(*     exists (card: nat) (inj: A -> nat), *)
(*     Injective inj /\ forall a (IN: is_some (f a)), ((inj a) < card)%nat }. *)
(* Program Definition add_finfun A B (add: B -> B -> B) (f g: finfun A B): finfun A B := *)
(*   exist _ (fun a => match `f a, `g a with *)
(*                     | Some x, None => Some x *)
(*                     | None, Some y => Some y *)
(*                     | Some x, Some y => Some (add x y) *)
(*                     | None, None => None *)
(*                     end) _. *)
(* Next Obligation. *)
(*   destruct f, g; ss. des. *)
(*   exists (card + card0)%nat. eexists (fun a => if (is_some (x a)) && (inj a <? card)%nat *)
(*                                                then inj a *)
(*                                                else (card + (inj0 a))%nat). *)
(*   esplits; eauto. *)
(*   - rr. ii. des_ifs; bsimpl; des; apply_all_once Nat.leb_le; apply_all_once Nat.leb_gt; *)
(*               apply_all_once e; apply_all_once e0; clarify; *)
(*               apply_all_once e1; apply_all_once e2; clarify. *)
(* Qed. *)




Module Sk.

  Inductive gdef: Type := Gfun | Gvar (gv: val).

  Definition t: Type := list (gname * gdef).

  Definition unit: t := nil.

  Definition add: t -> t -> t := @List.app _.

  (* Definition wf: t -> Prop := @List.NoDup _. *)
  Definition wf (sk: t): Prop := @List.NoDup _ (List.map fst sk).

  (*** TODO: It might be nice if Sk.t also constitutes a resource algebra ***)
  (*** At the moment, List.app is not assoc/commutative. We need to equip RA with custom equiv. ***)

  Definition load_mem (sk: t): Mem.t :=
    let n := List.length sk in
    Mem.mk
      (* (fun blk => if (blk <? n)%nat then (fun _ => None) else (fun _ => None)) *)
      (fun _ _ => None)
      (*** TODO: This simplified model doesn't allow function pointer comparsion.
           To be more faithful, we need to migrate the notion of "permission" from CompCert.
           CompCert expresses it with "nonempty" permission.
       ***)
      (*** TODO: When doing so, I would like to extend val with "Vfid (id: gname)" case.
           That way, I might be able to support more higher-order features (overriding, newly allocating function)
       ***)
      n
  .

  Definition load_skenv (sk: t): (SkEnv.t) :=
    let n := List.length sk in
    {|
      SkEnv.blk2id := fun blk => do '(ofs, _) <- (List.nth_error sk blk); Some ofs;
      SkEnv.id2blk := fun id => do '(blk, _) <- find_idx (fun '(id', _) => string_dec id id') sk; Some blk
    |}
  .

  Lemma load_skenv_wf
        sk
        (WF: wf sk)
    :
      <<WF: SkEnv.wf (load_skenv sk)>>
  .
  Proof.
    r in WF.
    rr. split; i; ss.
    - uo; des_ifs.
      + admit "ez".
      + admit "ez".
    - uo; des_ifs_safe. des_ifs.
      + destruct p0; ss. repeat f_equal. admit "ez".
      + admit "ez".
  Qed.

End Sk.
