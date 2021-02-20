Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.




(* Definition until (n: nat): list nat := mapi (fun n _ => n) (List.repeat tt n). *)


(*** TODO: move to Coqlib ***)
Definition map_fst A B C (f: A -> C): A * B -> C * B := fun '(a, b) => (f a, b).
Definition map_snd A B C (f: B -> C): A * B -> A * C := fun '(a, b) => (a, f b).


(** TODO: move to PCM.v **)
Declare Scope ra_scope.
Delimit Scope ra_scope with ra.
Notation " K ==> V' " := (URA.pointwise K V'): ra_scope.



Let _memRA: URA.t := (block ==> Z ==> (RA.excl val))%ra.
Compute (URA.car (t:=_memRA)).
Instance memRA: URA.t := URA.auth _memRA.
Compute (URA.car).

Definition points_to (loc: block * Z) (v: val): URA.car :=
  let (b, ofs) := loc in
  URA.white (M:=_memRA)
            (fun _b _ofs => if (dec _b b) && (dec _ofs ofs) then inl (Some v) else inr tt).

Definition points_tos (loc: block * Z) (vs: list val): URA.car :=
  let (b, ofs) := loc in
  URA.white (M:=_memRA)
            (fun _b _ofs => if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length vs))))%Z
                            then inl (List.nth_error vs (Z.to_nat (_ofs - ofs))) else inr tt).




(* Definition own {GRA: GRA.t} (whole a: URA.car (t:=GRA)): Prop := URA.extends a whole. *)

Notation "loc |-> v" := (points_to loc v) (at level 20).





Section PROOF.
  Context {Σ: GRA.t}.
  (*** TODO: move to proper place, together with "mk_simple" ***)
  (*** TODO: rename sb into spb ***)
  Definition mk_sb_simple (mn: string) {X: Type} (P: X -> Any.t -> Σ -> Prop) (Q: X -> Any.t -> Σ -> Prop) (measure: X -> ord)
             (body: list val -> itree (hCallE +' pE +' eventE) val): fspecbody := mk_specbody (mk_simple mn P Q measure) body.

End PROOF.



Section PROOF.
  Context `{@GRA.inG memRA Σ}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.

  (* Definition mem_inv: Σ -> Prop := *)
  (*   fun mr0 => exists mem0, mr0 = GRA.padding (URA.black (M:=_memRA) (inl mem0)). *)


  (*** TODO: morally, we want:
```
      sz <- trigger (Take nat);;
      assume(varg = [Vint (Z.of_nat sz)]);;
```
  ***)


  (* Definition allocF: list val -> itree Es val := *)
  (*   HoareFun "Mem" *)
  (*            (fun sz varg _ => varg = [Vint (Z.of_nat sz)]) *)
  (*            (fun sz vret rret => *)
  (*               exists b, vret = Vptr b 0 /\ *)
  (*               rret = GRA.padding (fold_left URA.add (mapi (fun n _ => (b, Z.of_nat n) |-> (Vint 0)) *)
  (*                                                           (List.repeat tt sz)) URA.unit)) *)
  (*            (fun _ => trigger (Choose _)) *)
  (* . *)

  (* Definition freeF: list val -> itree Es val := *)
  (*   HoareFun "Mem" *)
  (*            (fun '(b, ofs, v) varg rarg => varg = [Vptr b ofs] /\ *)
  (*                                           rarg = (GRA.padding ((b, ofs) |-> v))) *)
  (*            (top3) *)
  (*            (fun _ => trigger (Choose _)) *)
  (* . *)

  (* Definition loadF: list val -> itree Es val := *)
  (*   HoareFun "Mem" *)
  (*            (fun '(b, ofs, v) varg rarg => varg = [Vptr b ofs] /\ *)
  (*                                           rarg = (GRA.padding ((b, ofs) |-> v))) *)
  (*            (fun '(b, ofs, v) vret rret => rret = (GRA.padding ((b, ofs) |-> v)) /\ vret = v) *)
  (*            (fun _ => trigger (Choose _)) *)
  (* . *)

  (* Definition storeF: list val -> itree Es val := *)
  (*   HoareFun "Mem" *)
  (*            (fun '(b, ofs, v_old, v_new) varg rarg => *)
  (*               varg = [Vptr b ofs ; v_new] /\ rarg = (GRA.padding ((b, ofs) |-> v_old))) *)
  (*            (fun '(b, ofs, v_old, v_new) _ rret => rret = (GRA.padding ((b, ofs) |-> v_new))) *)
  (*            (fun _ => trigger (Choose _)) *)
  (* . *)

  Let alloc_spec: fspec := (mk_simple "Mem"
                                      (fun sz varg _ => varg = [Vint (Z.of_nat sz)]↑)
                                      (fun sz vret rret =>
                                         exists b, vret = (Vptr b 0)↑ /\
                                                   rret = GRA.padding (points_tos (b, 0%Z) (List.repeat (Vint 0) sz)))
                                      (fun _ => (ord_pure 1))).

  Let free_spec: fspec := (mk_simple "Mem"
                                     (fun '(b, ofs) varg rarg => exists v, varg = ([Vptr b ofs])↑ /\
                                                                           rarg = (GRA.padding ((b, ofs) |-> v)))
                                     (top3)
                                     (fun _ => (ord_pure 1))).

  Let load_spec: fspec := (mk_simple "Mem"
                                     (fun '(b, ofs, v) varg rarg => varg = ([Vptr b ofs])↑ /\
                                                                    rarg = (GRA.padding ((b, ofs) |-> v)))
                                     (fun '(b, ofs, v) vret rret => rret = (GRA.padding ((b, ofs) |-> v)) /\ vret = v↑)
                                     (fun _ => (ord_pure 1))).

  Let store_spec: fspec := (mk_simple
                              "Mem"
                              (fun '(b, ofs, v_new) varg rarg => exists v_old,
                                   varg = ([Vptr b ofs ; v_new])↑ /\ rarg = (GRA.padding ((b, ofs) |-> v_old)))
                              (fun '(b, ofs, v_new) _ rret => rret = (GRA.padding ((b, ofs) |-> v_new)))
                              (fun _ => (ord_pure 1))).

  Definition MemStb: list (gname * fspec) :=
    [("alloc", alloc_spec) ; ("free", free_spec) ; ("load", load_spec) ; ("store", store_spec)]
  .

  Definition MemSbtb: list (gname * fspecbody) :=
    [("alloc", mk_specbody alloc_spec (fun _ => trigger (Choose _)));
    ("free",   mk_specbody free_spec (fun _ => trigger (Choose _)));
    ("load",   mk_specbody load_spec (fun _ => trigger (Choose _)));
    ("store",   mk_specbody store_spec (fun _ => trigger (Choose _)))
    ]
  .






  (* Definition MemSbtb: list (gname * fspecbody) := *)
  (* [("alloc", mk_sb_simple "Mem" *)
  (*              (fun sz varg _ => varg = [Vint (Z.of_nat sz)]↑) *)
  (*              (fun sz vret rret => *)
  (*                 exists b, vret = (Vptr b 0)↑ /\ *)
  (*                           rret = GRA.padding (points_tos (b, 0%Z) (List.repeat (Vint 0) sz))) *)
  (*              (fun _ => (ord_pure 1)) *)
  (*              (fun _ => trigger (Choose _))) ; *)
  (* ("free", mk_sb_simple "Mem" *)
  (*             (fun '(b, ofs) varg rarg => exists v, varg = ([Vptr b ofs])↑ /\ *)
  (*                                                   rarg = (GRA.padding ((b, ofs) |-> v))) *)
  (*             (top3) *)
  (*             (fun _ => (ord_pure 1)) *)
  (*             (fun _ => trigger (Choose _))) ; *)
  (* ("load", mk_sb_simple "Mem" *)
  (*             (fun '(b, ofs, v) varg rarg => varg = ([Vptr b ofs])↑ /\ *)
  (*                                          rarg = (GRA.padding ((b, ofs) |-> v))) *)
  (*             (fun '(b, ofs, v) vret rret => rret = (GRA.padding ((b, ofs) |-> v)) /\ vret = v↑) *)
  (*             (fun _ => (ord_pure 1)) *)
  (*             (fun _ => trigger (Choose _))) ; *)
  (* ("store", mk_sb_simple *)
  (*             "Mem" *)
  (*              (fun '(b, ofs, v_new) varg rarg => exists v_old, *)
  (*                   varg = ([Vptr b ofs ; v_new])↑ /\ rarg = (GRA.padding ((b, ofs) |-> v_old))) *)
  (*              (fun '(b, ofs, v_new) _ rret => rret = (GRA.padding ((b, ofs) |-> v_new))) *)
  (*              (fun _ => (ord_pure 1)) *)
  (*              (fun _ => trigger (Choose _))) *)
  (* ] *)
  (* . *)

  (* Definition MemStb: list (gname * fspec) := List.map (map_snd fsb_fspec) MemSbtb. *)

  (* Definition MemFtb2: list (gname * fspec * (list val -> itree (hCallE +' eventE) val)) := *)
  (* [("alloc", mk "Mem" *)
  (*              (fun sz varg _ => varg = [Vint (Z.of_nat sz)]) *)
  (*              (fun sz vret rret => *)
  (*                 exists b, vret = Vptr b 0 /\ *)
  (*                           rret = GRA.padding (fold_left URA.add *)
  (*                                                         (mapi (fun n _ => (b, Z.of_nat n) |-> (Vint 0)) *)
  (*                                                               (List.repeat tt sz)) URA.unit)), (fun _ => trigger (Choose _))) ; *)
  (* ("free", mk "Mem" *)
  (*             (fun '(b, ofs, v) varg rarg => varg = [Vptr b ofs] /\ *)
  (*                                            rarg = (GRA.padding ((b, ofs) |-> v))) *)
  (*             (top3), (fun _ => trigger (Choose _))) ; *)
  (* ("load", mk "Mem" *)
  (*             (fun '(b, ofs, v) varg rarg => varg = [Vptr b ofs] /\ *)
  (*                                            rarg = (GRA.padding ((b, ofs) |-> v))) *)
  (*             (fun '(b, ofs, v) vret rret => rret = (GRA.padding ((b, ofs) |-> v)) /\ vret = v), (fun _ => trigger (Choose _))) ; *)
  (* ("store", mk "Mem" *)
  (*              (fun '(b, ofs, v_old, v_new) varg rarg => *)
  (*                 varg = [Vptr b ofs ; v_new] /\ rarg = (GRA.padding ((b, ofs) |-> v_old))) *)
  (*              (fun '(b, ofs, v_old, v_new) _ rret => rret = (GRA.padding ((b, ofs) |-> v_new))), (fun _ => trigger (Choose _))) *)
  (* ] *)
  (* . *)
  (* Goal MemFtb = MemFtb2. refl. Qed. *)

  Definition MemSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fsb) => (fn, fun_to_tgt MemStb fn fsb)) MemSbtb;
      (* [("alloc", allocF) ; ("free", freeF) ; ("load", loadF) ; ("store", storeF)]; *)
    ModSem.initial_mrs := [("Mem", (GRA.padding (URA.black (M:=_memRA) (fun _ _ => inr tt)), unit↑))];
  |}
  .

  Definition Mem: Mod.t := {|
    Mod.get_modsem := fun _ => MemSem; (*** TODO: we need proper handling of function pointers ***)
    Mod.sk := List.map (fun '(n, _) => (n, Sk.Gfun)) MemStb;
  |}
  .

End PROOF.
