Require Import Coqlib.
Require Import Universe.
Require Import PCM.

Set Implicit Arguments.



Module Mem.

  Definition t: Type := block -> Z -> option val.

End Mem.





Module SkEnv.

  Record t: Type := mk {
    ptr2id: val -> option ident;
    id2ptr: ident -> option val;
    wf: forall id ptr, id2ptr id = Some ptr <-> ptr2id ptr = Some id;
  }
  .

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





Module Sk.

  Definition t: Type := list ident.

  Global Program Instance RA: RA.t := {|
    RA.car := t;
    RA.add := @List.app _;
    RA.wf := @List.NoDup _;
  |}
  .
  Next Obligation.
    admit "".
  Qed.
  Next Obligation.
    admit "".
  Qed.
  Next Obligation.
    admit "".
  Qed.

  Definition link: t -> t -> t := admit "".

  Definition load (sk: t): (mem * ).
    (* t: Type; *)
    (* wf: t -> Prop; *)
    (* Linker:> Linker t; *)
    (* load_skenv: t -> Genv.t (fundef signature) unit; *)
    (* load_mem: t -> option mem; *)
    (* link_preserves_wf_sk: forall *)
    (*     sk0 sk1 sk_link *)
    (*     (WFSK0: wf sk0) *)
    (*     (WFSK1: wf sk1) *)
    (*     (LINK: link sk0 sk1 = Some sk_link) *)
    (*   , *)
    (*     (<<WF: wf sk_link>>) *)
    (* ; *)
    (* disj: t -> t -> Prop; *)
    (* link_disj: forall  *)
    (*     sk0 sk1 sk_link *)
    (*     (LINK: link sk0 sk1 = Some sk_link) *)
    (*   , *)
    (*     (<<DISJ: disj sk0 sk1>>) *)
    (* ; *)
    (* disj_linkorder: forall *)
    (*     sk0 sk1 sk_link *)
    (*     (DISJ: disj sk0 sk_link) *)
    (*     (LINK: linkorder sk1 sk_link) *)
    (*   , *)
    (*     (<<DISJ: disj sk0 sk1>>) *)
    (* ; *)

End Sk.



