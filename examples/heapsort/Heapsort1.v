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
    fun '(xs0, initval) =>
      let nmemb := length xs0 in
      xs1 <- ITree.iter (fun '(xs, par_i) =>
        if 2*par_i <=? nmemb
        then 
          child_i <- (
            if 2*par_i <? nmemb
            then
              child_val0 <- (nth_error xs (par_i*2 - 1))?;;
              child_val1 <- (nth_error xs (par_i*2))?;;
              if (child_val0 <? child_val1)%Z
              then Ret (par_i*2 + 1)
              else Ret (par_i*2)
            else Ret (par_i*2));;
          child_val <- (nth_error xs (child_i - 1))?;;
          par_val <- (nth_error xs (par_i - 1))?;;
          if Z.leb child_val par_val
          then Ret (inr xs)              
          else Ret (inl (swap xs (child_i - 1) (par_i - 1), child_i))
        else Ret (inr xs)
      ) (xs0, initval);;
      Ret xs1.

  Definition create_spec : fspec.
  Admitted.

  Definition heapify_body : (list Z * Z) -> itree Es (list Z) :=
    fun '(xs0, k) =>
    let nmemb := length xs0 in
    '(xs1, par_i) <- ITree.iter (fun '(xs, par_i) =>
      if par_i*2 <=? nmemb
      then
        if par_i*2 <? nmemb
        then
          child_l <- (nth_error xs (par_i*2 - 1))?;;
          child_r <- (nth_error xs (par_i*2))?;;
          let child_i := if (child_l <? child_r)%Z then par_i*2 + 1 else par_i*2 in
          child <- (nth_error xs (child_i - 1))?;;
          Ret (inl (upd xs (par_i - 1) child, child_i))
        else
          let child_i := par_i*2 in
          child <- (nth_error xs (child_i - 1))?;;
          Ret (inl (upd xs (par_i - 1) child, child_i))
      else Ret (inr (xs, par_i))
    ) (xs0, 1);;
    '(xs2, par_i) <- ITree.iter (fun '(xs, par_i) =>
      let child_i := par_i in
      let par_i := child_i / 2 in
      if (child_i =? 1)%nat
      then Ret (inr (upd xs (child_i - 1) k, par_i))
      else
        par <- (nth_error xs (par_i - 1))?;;
        if (k <? par)%Z
        then Ret (inr (upd xs (child_i - 1) k, par_i))
        else Ret (inl (upd xs (child_i - 1) par, par_i))
    ) (xs1, par_i);;
    Ret xs2.

  Definition heapify_spec : fspec.
  Admitted.

  Definition heapsort_body : list Z -> itree Es (list Z) :=
    fun xs0 =>
      if length xs0 <=? 1
      then Ret xs0
      else
        xs1 <- ITree.iter (fun '(xs, l) =>
          if (l =? 0)%nat
          then Ret (inr xs)
          else
            r <- trigger (Call "create" (xs, l)↑);;
            xs <- (r↓)?;;
            Ret (inl (xs, l - 1))
        ) (xs0, length xs0 / 2);;
        ys <- ITree.iter (fun '(xs, ys) =>
          if length xs <=? 1
          then Ret (inr (xs ++ ys))
          else
            m <- (head xs)?;;
            let k := last xs 0%Z in
            r <- trigger (Call "heapify" (removelast xs, k)↑);;
            xs <- (r↓)?;;
            Ret (inl (xs, m :: ys))
        ) (xs1, []);;
        Ret ys.

  Definition heapsort_spec : fspec.
  Admitted.

  Definition HeapsortSbtb :=
    [("create",  cfunU create_body);
    ("heapify",  cfunU heapify_body);
    ("heapsort", cfunU heapsort_body)
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
