Require Import Coqlib.
Require Import Universe.
Require Import PCM.

Set Implicit Arguments.



Module SkEnv.

  Record t: Type := mk {
    ptr2id: val -> option fname;
    id2ptr: fname -> option val;
  }
  .

  Definition wf (ske: t): Prop :=
    forall id ptr, ske.(id2ptr) id = Some ptr <-> ske.(ptr2id) ptr = Some id.

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

  Definition t: Type := list fname.

  Definition unit: t := nil.

  Definition add: t -> t -> t := @List.app _.

  Definition wf: t -> Prop := @List.NoDup _.

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
      (*** TODO: When doing so, I would like to extend val with "Vfid (id: fname)" case.
           That way, I might be able to support more higher-order features (overriding, newly allocating function)
       ***)
      n
  .

  Fixpoint _find_idx {A} (f: A -> bool) (l: list A) (acc: nat): option (nat * A) :=
    match l with
    | [] => None
    | hd :: tl => if (f hd) then Some (acc, hd) else _find_idx f tl (S acc)
    end
  .

  Definition find_idx {A} (f: A -> bool) (l: list A): option (nat * A) := _find_idx f l 0.

  Definition load_skenv (sk: t): (SkEnv.t) :=
    let n := List.length sk in
    {|
      SkEnv.ptr2id := fun v => match v with
                               | Vptr blk ofs => if (ofs =? 0)%Z
                                                 then List.nth_error sk blk
                                                 else None
                               | _ => None
                               end;
      SkEnv.id2ptr := fun id => do blkofs <- find_idx (string_dec id) sk; Some (Vptr (fst blkofs) 0)
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
    - uo; des_ifs. admit "ez".
    - uo; des_ifs_safe. apply Z.eqb_eq in Heq. subst. des_ifs.
      + destruct p; ss. repeat f_equal. admit "ez".
      + admit "ez".
  Qed.

End Sk.
