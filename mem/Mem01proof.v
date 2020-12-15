Require Import Mem0 Mem1 SimModSem Hoare.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
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

Ltac go := try first[pfold; econs; [..|M]; (Mskip ss); et; check_safe; ii; left|
                     pfold; econsr; [..|M]; (Mskip ss); et; check_safe; ii; left].
Ltac igo := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r).
Ltac force_l := pfold; econs; [..|M]; Mskip ss; et.
Ltac force_r := pfold; econsr; [..|M]; Mskip ss; et.
Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ} `{@GRA.inG (RA.excl Mem.t) Σ}.

  Let W: Type := (alist mname Σ) * (alist mname Σ).
  (* Eval compute in (@RA.car (RA.excl Mem.t)). *)
  Eval compute in (@RA.car Mem1._memRA).
  Inductive sim_loc: option val -> (option val + unit) -> Prop :=
  | sim_loc_present v: sim_loc (Some v) (inl (Some v))
  | sim_loc_absent: sim_loc None (inr tt)
  .

  Let wf: W -> Prop :=
    fun '(mrs_src0, mrs_tgt0) =>
      exists mem_src (mem_tgt: Mem.t),
        (<<SRC: mrs_src0 = Maps.add "mem" (GRA.padding (URA.black mem_src)) Maps.empty>>) /\
        (<<TGT: mrs_tgt0 = Maps.add "mem" (GRA.padding ((inl (Some mem_tgt)): URA.car (t:=RA.excl Mem.t)))
                                    Maps.empty>>) /\
        (<<SIM: forall b ofs, sim_loc ((mem_tgt.(Mem.cnts)) b ofs) (mem_src b ofs)>>)
  .

  Infix "⋅" := URA.add (at level 50, left associativity).
  Notation "(⋅)" := URA.add (only parsing).

  Theorem correct: ModSemPair.sim Mem1.mem Mem0.mem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. esplits; ss; et. ii. econs 2. }
    econs; ss.
    { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify.
      unfold alist_add, alist_remove; ss.
      unfold Mem1.allocF, Mem0.allocF.
      go. rename x into sz.
      unfold assume.
      igo.
      go. clarify. unfold HoareFun. go. rename x into rarg_src.
      unfold assume.
      igo.
      repeat go. clear_tac.
      Opaque URA.add.
      unfold unpadding, assume.
      igo.
      pfold. econsr; et. esplits; et.
      { ii. unfold GRA.padding. des_ifs. (*** TODO: should be trivial ***) }
      left.
      unfold unleftU. des_ifs; cycle 1.
      { exfalso. ss. unfold GRA.padding in Heq. des_ifs.
        admit "dependent type... use cast? lemma?".
        (* unfold PCM.GRA.cast_ra in *. *)
        (* unfold eq_rect_r, eq_rect, eq_sym in *. *)
        (* destruct (GRA.inG_prf). *)
        (* unfold eq_rect_r in *. ss. *)
        (* Set Printing All. *)
        (* erewrite rew_opp_l in Heq. *)
        (* unfold eq_rect_r in *. unfold eq_rect in *. unfold eq_sym in *. csc. *)
      }
      igo.
      assert(c = (Some mem_tgt)).
      { admit "dependent type". }
      clarify.
      unfold unwrapU. des_ifs. igo. des_ifs. unfold MPut. igo. repeat go.
      rename n into blk. rename z into ofs. rename mem_tgt into mem0. rename t into mem1.


      force_l. exists (Vptr blk 0). left.
      force_l.
      (* Eval compute in URA.car (t:=Mem1._memRA). *)
      (*** mret, fret ***)
      Check (mem_src: URA.car (t:=Mem1._memRA)).
      assert(sz = 1) by admit "let's consider only sz 1 case at the moment"; subst.
      set (fun _b _ofs => if (dec _b blk) && (dec _ofs 0%Z) then inl (Some (Vint 0)) else inr tt)
        as delta.
      eexists (GRA.padding (URA.black (URA.add (mem_src: URA.car (t:=Mem1._memRA)) delta)),
               GRA.padding
                 (fold_left URA.add
                            (mapi (fun n _ => (blk, Z.of_nat n) |-> Vint 0)
                                  (repeat () 1)) URA.unit)). left.
      igo. force_l.
      {
        replace (fun k => URA.unit) with (URA.unit (t:=Σ)) by ss.
        rewrite URA.unit_idl.
        rewrite GRA.padding_add.
        rewrite <- URA.unit_id.
        apply URA.updatable_add; cycle 1.
        { apply URA.updatable_unit. }
        eapply GRA.padding_updatable.
        ss. clarify.
        clear - Heq1.
        replace (@URA.frag Mem1._memRA (fun _ _ => @inr (option val) unit tt)) with
            (URA.unit (t:=Mem1.memRA)) by ss.
        rewrite URA.unit_idl.
        fold delta.
        eapply URA.auth_alloc2.
        admit "wf -- Need to know mem_src is wf. (1) Add checkwf, or (2) add wf in W.wf.
I think (1) is better; in (2), it seems like we are doing the same reasoning again
   ".
      }
      left. ss. fold delta. clarify.
      force_l.
      exists (GRA.padding (URA.white (delta: URA.car(t:=Mem1._memRA)))). left.
      unfold guarantee. igo.
      force_l. esplits; ss.
      (* { ss. f_equal. *)
      (*   replace (@URA.frag Mem1._memRA (fun (_ : nat) (_ : Z) => @inr (option val) unit tt)) with *)
      (*       (URA.unit: URA.car (t:=Mem1.memRA)) by ss. *)
      (*   rewrite URA.unit_idl. *)
      (*   unfold delta. eauto. *)
      (* } *)
      left.
      force_l.
      { instantiate (1:= GRA.padding _). rewrite GRA.padding_add. f_equal. }
      left.
      force_r.
      (* { eapply URA.updatable_add. *)
      (*   - eapply GRA.padding_updatable. clear - H. *)
      (*     (** TODO: this should be a lemma **) *)
      (*     hexploit RA.excl_updatable; et. intro A. des. *)
      (*     (*** TODO: RA.updatable --> URA.updatable ***) *)
      (*     admit "ez". *)
      (*   - refl. *)
      (* } *)
      (* left. *)
      (* pfold. econs; et. *)
      rr. esplits; ss; et. ii.
      hexploit (SIM b ofs); et. intro A. inv A.
      {
        assert(T: Mem.cnts mem1 b ofs = Some v).
        { admit "ez: memory model". }
        rewrite T.
        Local Transparent URA.add.
        ss. des_ifs.
        Local Opaque URA.add.
        + unfold delta in *. des_ifs. bsimpl. des. des_sumbool. clarify.
          admit "ez: memory model".
        + econs.
      }
      destruct (classic (b = blk /\ ofs = 0%Z)).
      { des. clarify.
        assert(T: Mem.cnts mem1 blk 0 = Some (Vint 0)).
        { admit "ez: memory model". }
        rewrite T.
        Local Transparent URA.add.
        ss. des_ifs.
        Local Opaque URA.add.
        unfold delta. ss. des_ifs; bsimpl; des; des_sumbool; ss; econs.
      }
      Psimpl. des; clarify.
      {
        assert(T: Mem.cnts mem1 b 0 = None).
        { admit "ez: memory model". }
        rewrite T.
        Local Transparent URA.add.
        ss. des_ifs.
        Local Opaque URA.add.
        unfold delta. ss. des_ifs; bsimpl; des; des_sumbool; ss; econs.
      }
      {
        assert(T: Mem.cnts mem1 b ofs = None).
        { admit "ez: memory model". }
        rewrite T.
        Local Transparent URA.add.
        ss. des_ifs.
        Local Opaque URA.add.
        unfold delta. ss. des_ifs; bsimpl; des; des_sumbool; ss; econs.
      }
    }
    econs; ss.
    { admit "free". }
    econs; ss.
    { admit "load". }
  Unshelve.
    all: ss.
    all: try (by repeat econs; et).
  Unshelve.
    all: try (by repeat econs; et).
  Qed.

End SIMMODSEM.


