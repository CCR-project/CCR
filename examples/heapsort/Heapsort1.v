Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import HeapsortHeader.

Set Implicit Arguments.

Section HEAPSORT.
  Context `{Σ : GRA.t}.
         
  Definition create_body : list val -> itree hEs val.
  Admitted.

  Definition create_spec : fspec.
  Admitted.

  Definition look (xs : list Z) (n : nat) : option Z :=
    match n with
    | O => None
    | S n' => nth_error xs n'
    end.

  Definition heapify_body : (list Z * Z) -> itree hEs (list Z) :=
    fun '(base, k) =>
    let nmemb : nat := length base in
    '(base, par_i) <- ITree.iter (fun '(base, par_i) =>
      if Nat.leb (par_i * 2) nmemb
      then (
        if Nat.ltb (par_i * 2) nmemb
        then (
          child_l <- (look base (par_i * 2))?;;
          child_r <- (look base (par_i * 2 + 1))?;;
          let child_i : nat := if Z.ltb child_l child_r then (par_i * 2) else (par_i * 2 + 1) in
          Ret (inl (swap base child_i par_i, child_i))
        )
        else (
          let child_i : nat := par_i * 2 + 1 in
          Ret (inl (swap base child_i par_i, child_i))
        )
      )
      else Ret (inr (base, par_i))
    ) (k :: tail base, 1%nat);;
    '(base, par_i) <- ITree.iter (fun '(base, par_i) =>
      let child_i : nat := par_i in
      let par_i : nat := child_i / 2 in
      if Nat.eqb child_i 1 
      then (
        par <- (look base par_i)?;;
        if Z.ltb k par
        then Ret (inr (base, par_i))
        else Ret (inl (swap base child_i par_i, par_i))
      )
      else (
        Ret (inl (swap base child_i par_i, par_i))
      )
    ) (base, par_i);;
    Ret base.

  Definition heapify_spec : fspec.
  Admitted.

  Definition heapsort_body : list Z -> itree hEs (list Z) :=
    fun xs =>
      heap <- ITree.iter (fun '(xs, l) =>
                           if Z.eqb l 0
                           then Ret (inr xs)
                           else xs' <- trigger (Call "create" (xs, l)↑);;
                                xs'' <- (xs'↓)?;;
                                Ret (inl (xs'', l - 1))%Z
                        )
                        (xs, Z.of_nat (length xs / 2));;
      ys <- ITree.iter (fun '(xs, ys) =>
                         if Nat.eqb (length xs) 0
                         then Ret (inr ys)
                         else
                           let k := last xs 0%Z in
                           xs' <- trigger (Call "heapify" (removelast xs, k)↑);;
                           xs'' <- (xs'↓)?;;
                           Ret (inl (xs'', k :: ys))
                      )
                      (heap, []);;
      Ret ys.

  Definition heapsort_spec : fspec.
  Admitted.
  
  Definition HeapsortSbtb : list (gname * fspecbody) :=
    [("create", mk_specbody create_spec (cfunN create_body));
    ("heapify", mk_specbody heapify_spec (cfunN heapify_body));
    ("heapsort", mk_specbody heapsort_spec (cfunN heapsort_body))
    ].

  Definition SHeapsortSem : SModSem.t.
  Admitted.

  Definition SHeapsort : SMod.t.
  Admitted.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Heapsort : Mod.t := SMod.to_tgt GlobalStb SHeapsort.
End HEAPSORT.
