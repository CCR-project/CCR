Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior Hoare.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.

Definition map_fst A0 A1 B (f: A0 -> A1): (A0 * B) -> (A1 * B) := fun '(a, b) => (f a, b).
Definition map_snd A B0 B1 (f: B0 -> B1): (A * B0) -> (A * B1) := fun '(a, b) => (a, f b).
(*** TODO: Somehow use case_ ??? ***)

Section CANCEL.

  Context `{Σ: GRA.t}.

  Variant hCallE: Type -> Type :=
  | hCall (mn: mname) (P: list val -> Σ -> Prop) (Q: list val -> Σ -> val -> Σ -> Prop)
          (fn: fname) (varg: list val): hCallE val
  .

  (* Definition handle_hCallE E `{callE -< E} `{rE -< E} `{eventE -< E}: hCallE ~> itree E := *)
  Definition handle_hCallE_tgt: hCallE ~> itree Es :=
    fun _ '(hCall mn P Q fn varg) => (HoareCall mn P Q fn varg)
  .

  Definition interp_hCallE_tgt: itree (hCallE +' callE +' eventE) ~> itree Es :=
    interp (case_ (bif:=sum1) handle_hCallE_tgt
                  (case_ (bif:=sum1) ((fun T X => trigger X): callE ~> itree Es)
                         ((fun T X => trigger X): eventE ~> itree Es)))
  .

  Let body_to_tgt (body: itree (hCallE +' callE +' eventE) unit): itree Es unit :=
    interp_hCallE_tgt body
  .



  Definition handle_hCallE_src: hCallE ~> itree Es :=
    fun _ '(hCall _ _ _ fn varg) => (HoareCallCanceled fn varg)
  .

  Definition interp_hCallE_src: itree (hCallE +' callE +' eventE) ~> itree Es :=
    interp (case_ (bif:=sum1) handle_hCallE_tgt
                  (case_ (bif:=sum1) ((fun T X => trigger X): callE ~> itree Es)
                         ((fun T X => trigger X): eventE ~> itree Es)))
  .

  Let body_to_src (body: itree (hCallE +' callE +' eventE) unit): itree Es unit :=
    interp_hCallE_src body
  .

  (*** spec table ***)
  Record funspec: Type := mk {
    mn: mname;
    precond: list val -> Σ -> Prop;
    postcond: list val -> Σ -> val -> Σ -> Prop;
    body: itree (hCallE +' callE +' eventE) unit;
    fun_to_tgt: (list val -> itree Es val) := HoareFun mn precond postcond (body_to_tgt body);
    fun_to_src: (list val -> itree Es val) := HoareFunCanceled (body_to_src body);
  }
  .
(*** NOTE:
body can execute callE and eventE events.
Notably, this implies (1) body can actually call a function not through HoareCall, but directly, and
(2) it can also execute UB.
With this flexibility, the client code can naturally be included in our "type-checking" framework.
Also, note that body cannot execute "rE" on its own. This is intended.
***)

  (* Variable stb: fname -> option funspec. *)
  (*** TODO: I wanted to use above definiton, but doing so makes defining ms_src hard ***)
  (*** We can fix this by making ModSem.fnsems to a function, but doing so will change the type of
       ModSem.add to predicate (t -> t -> t -> Prop), not function.
       - Maybe not. I thought one needed to check uniqueness of fname at the "add",
         but that might not be the case.
         We may define fnsems: string -> option (list val -> itree Es val).
         When adding two ms, it is pointwise addition, and addition of (option A) will yield None when both are Some.
 ***)
  (*** TODO: try above idea; if it fails, document it; and refactor below with alist ***)
  Variable stb: list (fname * funspec).

  Variable md_tgt: Mod.t.
  Let ms_tgt: ModSem.t := (Mod.get_modsem md_tgt (Sk.load_skenv md_tgt.(Mod.sk))).

  Hypothesis WTY: ms_tgt.(ModSem.fnsems) = List.map (map_snd fun_to_tgt) stb.

  Definition ms_src: ModSem.t := {|
    ModSem.fnsems := List.map (map_snd fun_to_src) stb;
    ModSem.initial_mrs := List.map (map_snd (fun _ => ε)) ms_tgt.(ModSem.initial_mrs);
    (*** note: we don't use resources, so making everything as a unit ***)
  |}
  .

  Definition md_src: Mod.t := {|
    Mod.get_modsem := fun _ => ms_src;
    Mod.sk := Sk.unit;
    (*** It is already a whole-program, so we don't need Sk.t anymore. ***)
    (*** Note: Actually, md_tgt's sk could also have been unit, which looks a bit more uniform. ***)
  |}
  .

  Theorem adequacy_type: Beh.of_program (Mod.interp md_tgt) <1= Beh.of_program (Mod.interp md_src).
  Proof.
    admit "TODO".
  Qed.

End CANCEL.













(* Section MOD. *)

(*   Context `{Σ: GRA.t}. *)

(*   Variable md: Mod.t. *)
(*   Variable stb: fname -> option funspec. *)

(*   Hypothesis WTY: Forall welltyped ms.(ModSem.fnsems). *)

(* End MOD. *)



(*   Variable mn_caller mn_callee: mname. *)
(*   Variable P: Σ -> Prop. *)
(*   (*** TODO: Maybe P should be able to depend on list val ***) *)
(*   (*** TODO: name it... htree (hoare tree), hktree (hoare ktree)? ***) *)
(*   Variable Q: val -> Σ -> Prop. *)
(*   Variable fn: fname. *)

(*   Let W: Type := (alist mname Σ) * (alist mname Σ). *)
(*   Let wf: W -> Prop := *)
(*     fun '(mrs_src0, mrs_tgt0) => *)
(*       exists _mr_caller_src _mr_caller_tgt _mr_callee_src _mr_callee_tgt, *)
(*         (<<SRC: mrs_src0 = Maps.add mn_callee _mr_callee_src *)
(*                                     (Maps.add mn_caller _mr_caller_src Maps.empty) *)
(*                                     >>) /\ *)
(*         (<<TGT: mrs_tgt0 = Maps.add mn_callee _mr_callee_tgt *)
(*                                     (Maps.add mn_caller _mr_caller_tgt Maps.empty) *)
(*                                     >>) *)
(*   . *)
(*   Hypothesis DIF: mn_caller <> mn_callee. *)

(*   Goal sim_fsem wf (fun _ => Ret (Vint 0)) (fun _ => (HoareCall mn_caller P Q fn [])). *)
(*   Proof. *)
(*     ii. clarify. exists 100. *)
(*     ss. des. clarify. *)
(*     force_r. ii. des_ifs. left. rename c into marg_caller. rename c0 into farg_caller. *)
(*     force_r. *)
(*     { unfold rel_dec. ss. instantiate (1:=_mr_caller_tgt). *)
(*       des_ifs; bsimpl; des; des_sumbool; ss; clarify. *)
(*       - unfold rel_dec. ss. des_ifs; bsimpl; des; des_sumbool; ss; clarify. *)
(*     } *)
(*     ii. left. *)
(*     go. rename x into rarg. *)
(*     repeat go. *)
(*     unfold guarantee. igo. *)
(*     go. *)





(*     assert(trigger (Call fn []) = HoareFun mn_callee P Q (Ret tt)). *)
(*     { admit "call inline". } *)
(*     rewrite H. unfold HoareFun. igo. *)
(*     replace fr_tgt1 with (URA.unit (t:=Σ)) by admit "push frame". *)
(*     force_r. *)
(*     exists rarg. left. *)
(*     igo. *)
(*     force_r. left. *)
(*     unfold assume. igo. *)
(*     force_r. esplits; et. left. *)
(*     force_r. intro vret. left. *)
(*     igo. *)
(*     force_r. intro tmp. destruct tmp as [mret_callee fret_callee]. left. *)
(*     igo. force_r. *)
(*     { unfold rel_dec. ss. instantiate (1:=_mr_callee_tgt). *)
(*       repeat (unfold rel_dec in *; ss; des_ifs; bsimpl; des; des_sumbool; ss; clarify). *)
(*     } *)
(*     i. rewrite URA.unit_idl in UPD0. *)
(*     left. force_r. intro rret. left. *)
(*     igo. unfold guarantee. igo. force_r. i. left. *)
(*     force_r. intro fret_garbage; i. *)
(*     left. *)


(*     replace fret_garbage with fr_tgt1 by admit "pop frame". *)
(*     force_r. exists rret. left. force_r. left. igo. force_r. *)
(*     esplits; et. left. *)
(*   Abort. *)

(* End CANCEL. *)
