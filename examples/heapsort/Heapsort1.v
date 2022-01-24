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

  Locate "?".

  Check unwrapU.

  Definition heapify_body : list val -> itree hEs val :=
    fun varg =>
    '(base, (nmemb, k)) <- (pargs [Tptr; Tint; Tint] varg)?;;
    `loop1_ret : _ <- ITree.iter (fun loop1_arg =>
      '(par_i, (child_i, (par, child))) <- (pargs [Tint; Tint; Tptr; Tptr] loop1_arg)?;;
      'child_i_val <- (vmul (Vint par_i) (Vint 2))?;;
      'child_i <- (parg Tint child_i_val)?;;
      if Z.leb child_i nmemb
      then Ret (inr [Vint par_i; Vint child_i; Vptr (fst par) (snd par); Vptr (fst child) (snd child)])
      else (
        'child_val <- (vadd (Vptr (fst base) (snd base)) (Vint child_i))?;;
        'child <- (parg Tptr child_val)?;;
(*     if (child_i < nmemb && *child < *(child+1)) {
          ++child;
          ++child_i;
        }
        par = base + par_i;
        *par = *child; *)
        'par_i <- (parg Tint (Vint child_i))?;;
        Ret (inl [Vint par_i; Vint child_i; Vptr (fst par) (snd par); Vptr (fst child) (snd child)])
      )
    ) [Vint 1; Vundef; Vundef; Vundef];;
(*  for (;;) {
      child_i = par_i;
      par_i = child_i / 2;
      child = base + child_i;
      par = base + par_i;
      if (child_i == 1 || k < *par) {
        *child = k;
        break;
      }
      *child = *par;
    } *)
    Ret Vundef.

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
