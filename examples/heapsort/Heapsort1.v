Require Import Coqlib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import HeapsortHeader.
Require Import ConvC2ITree.
Require Import Clight_Mem0.
Require Import Clight_Mem1.
From compcert Require Import Ctypes Floats Integers Values Memory.

Set Implicit Arguments.

Section HEAPSORT.

  Context `{Σ : GRA.t}.
  Context `{H : @GRA.inG memRA Σ}. 

  Coercion Int64.intval : Int64.int >-> Z.
  Coercion Int.intval : Int.int >-> Z.
  Coercion Ptrofs.intval : Ptrofs.int >-> Z.

  Definition encode_list vlist : list memval := flat_map (encode_val AST.Mint32) vlist. 
  
  Definition is_arr (ll : val) (xs : list val) :=
    (∃ (b :block) (ofs : ptrofs),
        ⌜ll = Vptr b ofs⌝ ** OwnM ((b, Ptrofs.intval ofs) |-> (encode_list xs)))%I.
  
  Definition create_body : list Z * nat -> itree (hAPCE +' Es) (list Z) :=
    fun '(xs0, initval) =>
      let nmemb := length xs0 in
      xs1 <- @ITree.iter (hAPCE +' Es) (list Z) (list Z * nat) (fun '(xs, par_i) =>
        if 2*par_i <=? nmemb
        then 
          child_i <- (
            if 2*par_i <? nmemb
            then
              child_val0 <- (nth_error xs (par_i*2 - 1))?;;
              child_val1 <- (nth_error xs (par_i*2))?;;
              if (child_val0 <? child_val1)%Z
              then Ret (par_i*2 + 1)%nat
              else Ret (par_i*2)%nat
            else Ret (par_i*2)%nat);;
          child_val <- (nth_error xs (child_i - 1))?;;
          par_val <- (nth_error xs (par_i - 1))?;;
          if Z.leb child_val par_val
          then Ret (inr xs)              
          else Ret (inl (swap xs (child_i - 1) (par_i - 1), child_i))
        else Ret (inr xs)
      ) (xs0, initval);;
      Ret xs1.

  Definition create_spec : fspec :=
    {|meta := positive * Ptrofs.int * (list int) * Int64.int * Int64.int;
      
      measure := fun _ => ord_pure 1%nat;
      
      precond := fun _ x arg varg =>
                   let  '(p, z, l, size, iidx) := x in
                   (⌜ arg = (Vptr p z, Vlong size, Vlong iidx)↑
                   /\ varg = (map Int.intval l, Z.to_nat iidx)↑
                   /\ length l = Z.to_nat size ⌝
                   ** is_arr (Vptr p z) (map Vint l))%I;

      postcond := fun _ x ret vret =>
                    let '(p, z, _, size, _) := x in
                    (∃ l' : list int,
                        ⌜ ret = Vundef↑ /\ vret = (map Int.intval l')↑
                        /\ length l' = Z.to_nat size⌝
                        ** is_arr (Vptr p z) (map Vint l'))%I
    |}.



  Definition heapify_body : (list Z * Z) -> itree (hAPCE +' Es) (list Z) :=
    fun '(xs0, k) =>
    let nmemb := length xs0 in
    '(xs1, par_i) <- @ITree.iter (hAPCE +' Es) (list Z * nat) (list Z * nat) (fun '(xs, par_i) =>
      if par_i*2 <=? nmemb
      then
        if par_i*2 <? nmemb
        then
          child_l <- (nth_error xs (par_i*2 - 1))?;;
          child_r <- (nth_error xs (par_i*2))?;;
          let child_i := (if (child_l <? child_r)%Z then par_i*2 + 1 else par_i*2)%nat in
          child <- (nth_error xs (child_i - 1))?;;
          Ret (inl (upd xs (par_i - 1) child, child_i))
        else
          let child_i := (par_i*2)%nat in
          child <- (nth_error xs (child_i - 1))?;;
          Ret (inl (upd xs (par_i - 1) child, child_i))
      else Ret (inr (xs, par_i))
    ) (xs0, 1%nat);;
    '(xs2, par_i) <- @ITree.iter (hAPCE +' Es) (list Z * nat) (list Z * nat) (fun '(xs, par_i) =>
      let child_i := par_i in
      let par_i := (child_i / 2)%nat in
      if (child_i =? 1)%nat
      then Ret (inr (upd xs (child_i - 1) k, par_i))
      else
        par <- (nth_error xs (par_i - 1))?;;
        if (k <? par)%Z
        then Ret (inr (upd xs (child_i - 1) k, par_i))
        else Ret (inl (upd xs (child_i - 1) par, par_i))
    ) (xs1, par_i%nat);;
    Ret xs2.

  Definition heapify_spec : fspec :=
    {| meta := block * ptrofs * list int * Int64.int * int;
       measure := fun _ => ord_pure 1%nat;
       precond := fun _ x arg varg =>
                    let '(p, z, l, size, k) := x in
                    (⌜ arg = (Vptr p z, Vlong size, Vint k)↑
                     /\ varg = (map Int.intval l, k : Z)↑
                     /\ length l = Z.to_nat size ⌝
                     ** is_arr (Vptr p z) (map Vint l))%I;
       postcond := fun _ x ret vret =>
                     let '(p, z, _, size, _) := x in
                     (∃ l' : list int,
                         ⌜ ret = Vundef↑ /\ vret = (map Int.intval l')↑
                         /\ length l' = Z.to_nat size ⌝
                         ** is_arr (Vptr p z) (map Vint l'))%I
    |}.

  Definition heapsort_body : list Z -> itree (hAPCE +' Es) (list Z) :=
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
            Ret (inl (xs, (l - 1)%nat))
        ) (xs0, (length xs0 / 2)%nat);;
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

  Definition heapsort_spec : fspec :=
    {| meta := block * ptrofs * list int * Int64.int;
       measure := fun _ => ord_pure 1%nat;
       precond := fun _ x arg varg =>
                    let '(p, z, l, size) := x in
                    (⌜ arg = (Vptr p z, Vlong size)↑
                     /\ varg = (map Int.intval l)↑
                     /\ length l = Z.to_nat size ⌝
                     ** is_arr (Vptr p z) (map Vint l))%I;
       postcond := fun _ x ret vret =>
                     let '(p, z, _, size) := x in
                     (∃ l' : list int,
                         ⌜ ret = Vundef↑ /\ vret = (map Int.intval l')↑
                         /\ length l' = Z.to_nat size ⌝
                         ** is_arr (Vptr p z) (map Vint l'))%I
    |}.

  Definition HeapsortSbtb :=
    [("create",  cfunU create_body);
    ("heapify",  cfunU heapify_body);
    ("heapsort", cfunU heapsort_body)
    ].
  

  Definition SHeapsortSbtb : list (gname * fspecbody) :=
    [("create",  mk_specbody create_spec (cfunU create_body));
    ("heapify",  mk_specbody heapify_spec (cfunU heapify_body));
    ("heapsort", mk_specbody heapsort_spec (cfunU heapsort_body))
    ].
  
  Definition SHeapsortStb : list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun fsb => fsb.(fsb_fspec) : fspec)) SHeapsortSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition SHeapsortSem : SModSem.t := {|
    SModSem.fnsems := SHeapsortSbtb;
    SModSem.mn := "Heapsort";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}.

  Definition SHeapsort : SMod.t := {|
    SMod.get_modsem := fun _ => SHeapsortSem;
    SMod.sk := Sk.unit;
  |}.

  Definition Heapsort : Mod.t := SMod.to_src SHeapsort.

  Definition Heapsort_to0 stb : Mod.t := (SMod.to_tgt stb) SHeapsort.
  
End HEAPSORT.
