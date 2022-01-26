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
         
  Definition create_body : list Z * nat -> itree Es (list Z) :=
    fun '(base, i) =>
      let nmemb : nat := length base in
      initval <- Ret(Z.to_nat i);;
      base <- ITree.iter(fun '(base, par_i) =>
          if Nat.leb (2*par_i) nmemb
          then (
              child_i <- (if Nat.ltb (2*par_i) nmemb
                         then (child_val0 <- (lookup_1 base (par_i*2))?;;
                               child_val1 <- (lookup_1 base (par_i*2 +1))?;;
                               if Z.ltb child_val0 child_val1
                               then Ret(par_i*2 +1) else Ret(par_i*2)
                              )
                         else Ret (par_i*2));;
              child_val <- (lookup_1 base child_i)?;;
              par_val <- (lookup_1 base par_i)?;;
              if Z.leb child_val par_val
              then Ret (inr base)                                            
              else Ret (inl (swap_1 base child_i par_i, child_i))
            )
          else Ret (inr base)
                       ) (base, initval);;Ret base.

  Definition create_spec : fspec.
  Admitted.
  
  Definition heapify_body : (list Z * Z) -> itree Es (list Z) :=
    fun '(base, k) =>
    let nmemb : nat := length base in
    '(base, par_i) <- ITree.iter (fun '(base, par_i) =>
      if Nat.leb (par_i * 2) nmemb
      then (
        if Nat.ltb (par_i * 2) nmemb
        then (
          child_l <- (lookup_1 base (par_i * 2))?;;
          child_r <- (lookup_1 base (par_i * 2 + 1))?;;
          let child_i : nat := if Z.ltb child_l child_r then (par_i * 2 + 1) else (par_i * 2) in
          Ret (inl (swap_1 base child_i par_i, child_i))
        )
        else (
          let child_i : nat := par_i * 2 in
          Ret (inl (swap_1 base child_i par_i, child_i))
        )
      )
      else Ret (inr (base, par_i))
    ) (k :: tail base, 1%nat);;
    '(base, par_i) <- ITree.iter (fun '(base, par_i) =>
      let child_i : nat := par_i in
      let par_i : nat := child_i / 2 in
      if Nat.eqb child_i 1 
      then Ret (inr (base, par_i))
      else (
        par <- (lookup_1 base par_i)?;;
        if Z.ltb k par
        then Ret (inr (base, par_i))
        else Ret (inl (swap_1 base child_i par_i, par_i))
      )
    ) (base, par_i);;
    Ret base.

  Definition heapify_spec : fspec.
  Admitted.

  Definition heapsort_body : list Z -> itree Es (list Z) :=
    fun xs =>
      heap <- ITree.iter (fun '(xs, l) =>
                           if Nat.eqb l 0
                           then Ret (inr xs)
                           else xs' <- trigger (Call "create" (xs, l)↑);;
                                xs'' <- (xs'↓)?;;
                                Ret (inl (xs'', l - 1))
                        )
                        (xs, length xs / 2);;
      ys <- ITree.iter (fun '(heap, ys) =>
                         if Nat.leb (length heap) 1
                         then Ret (inr (heap ++ ys))
                         else
                           m <- (head heap)?;;
                           let k := last heap 0%Z in
                           heap_ <- trigger (Call "heapify" (removelast heap, k)↑);;
                           heap <- (heap_↓)?;;
                           Ret (inl (heap, m :: ys))
                      )
                      (heap, []);;
      Ret ys.

  Definition heapsort_spec : fspec.
  Admitted.

  Definition main_body : itree Es Any.t :=
    ys <- trigger (Call "heapsort" ([7;4;5;3;1;6;0;3;6;8;1;6;8;4;7;9;2;5;7]%Z : list Z)↑);;
    r <- trigger (Syscall "print" ys top1);;
    Ret r.
  
  Definition HeapsortSbtb :=
    [("create",  cfunU create_body);
    ("heapify",  cfunU heapify_body);
    ("heapsort", cfunU heapsort_body);
    ("main", fun _ => main_body)
    ].

  Definition HeapsortSem : ModSem.t := {|
    ModSem.fnsems := HeapsortSbtb;
    ModSem.mn := "Heapsort";
    ModSem.initial_st := tt↑;
  |}.

  Definition Heapsort : Mod.t := {|
    Mod.get_modsem := fun _ => HeapsortSem;
    Mod.sk := Sk.unit;
  |}.

End HEAPSORT.

Section Ext.

  Definition heapsort_main := ModSemL.initial_itr (ModL.enclose (Mod.add_list [Heapsort])) None.

End Ext.
