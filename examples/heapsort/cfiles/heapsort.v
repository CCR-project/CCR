From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.10".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "heapsort.c".
  Definition normalized := false.
End Info.

Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _base : ident := $"base".
Definition _child : ident := $"child".
Definition _child_i : ident := $"child_i".
Definition _create : ident := $"create".
Definition _heapify : ident := $"heapify".
Definition _heapsort : ident := $"heapsort".
Definition _initval : ident := $"initval".
Definition _k : ident := $"k".
Definition _l : ident := $"l".
Definition _main : ident := $"main".
Definition _nmemb : ident := $"nmemb".
Definition _par : ident := $"par".
Definition _par_i : ident := $"par_i".
Definition _tmp : ident := $"tmp".
Definition _vbase : ident := $"vbase".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.

Definition f_create := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_base, (tptr tint)) :: (_nmemb, tulong) ::
                (_initval, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_par_i, tulong) :: (_child_i, tulong) ::
               (_par, (tptr tint)) :: (_child, (tptr tint)) ::
               (_tmp, tint) :: (_t'2, tint) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _par_i (Etempvar _initval tulong))
  (Sloop
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Ecast
              (Ebinop Omul (Etempvar _par_i tulong)
                (Econst_int (Int.repr 2) tint) tulong) tulong))
          (Sset _child_i (Etempvar _t'1 tulong)))
        (Sifthenelse (Ebinop Ole (Etempvar _t'1 tulong)
                       (Etempvar _nmemb tulong) tint)
          Sskip
          Sbreak))
      (Ssequence
        (Sset _child
          (Ebinop Oadd (Etempvar _base (tptr tint))
            (Etempvar _child_i tulong) (tptr tint)))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _child_i tulong)
                           (Etempvar _nmemb tulong) tint)
              (Sset _t'2
                (Ecast
                  (Ebinop Olt (Ederef (Etempvar _child (tptr tint)) tint)
                    (Ederef
                      (Ebinop Oadd (Etempvar _child (tptr tint))
                        (Econst_int (Int.repr 1) tint) (tptr tint)) tint)
                    tint) tbool))
              (Sset _t'2 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'2 tint)
              (Ssequence
                (Sset _child
                  (Ebinop Oadd (Etempvar _child (tptr tint))
                    (Econst_int (Int.repr 1) tint) (tptr tint)))
                (Sset _child_i
                  (Ebinop Oadd (Etempvar _child_i tulong)
                    (Econst_int (Int.repr 1) tint) tulong)))
              Sskip))
          (Ssequence
            (Sset _par
              (Ebinop Oadd (Etempvar _base (tptr tint))
                (Etempvar _par_i tulong) (tptr tint)))
            (Ssequence
              (Sifthenelse (Ebinop Ole
                             (Ederef (Etempvar _child (tptr tint)) tint)
                             (Ederef (Etempvar _par (tptr tint)) tint) tint)
                Sbreak
                Sskip)
              (Ssequence
                (Sset _tmp (Ederef (Etempvar _par (tptr tint)) tint))
                (Ssequence
                  (Sassign (Ederef (Etempvar _par (tptr tint)) tint)
                    (Ederef (Etempvar _child (tptr tint)) tint))
                  (Sassign (Ederef (Etempvar _child (tptr tint)) tint)
                    (Etempvar _tmp tint)))))))))
    (Sset _par_i (Etempvar _child_i tulong))))
|}.

Definition f_heapify := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_base, (tptr tint)) :: (_nmemb, tulong) :: (_k, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_par_i, tulong) :: (_child_i, tulong) ::
               (_par, (tptr tint)) :: (_child, (tptr tint)) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _par_i (Ecast (Econst_int (Int.repr 1) tint) tulong))
    (Sloop
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Ecast
                (Ebinop Omul (Etempvar _par_i tulong)
                  (Econst_int (Int.repr 2) tint) tulong) tulong))
            (Sset _child_i (Etempvar _t'1 tulong)))
          (Sifthenelse (Ebinop Ole (Etempvar _t'1 tulong)
                         (Etempvar _nmemb tulong) tint)
            Sskip
            Sbreak))
        (Ssequence
          (Sset _child
            (Ebinop Oadd (Etempvar _base (tptr tint))
              (Etempvar _child_i tulong) (tptr tint)))
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _child_i tulong)
                             (Etempvar _nmemb tulong) tint)
                (Sset _t'2
                  (Ecast
                    (Ebinop Olt (Ederef (Etempvar _child (tptr tint)) tint)
                      (Ederef
                        (Ebinop Oadd (Etempvar _child (tptr tint))
                          (Econst_int (Int.repr 1) tint) (tptr tint)) tint)
                      tint) tbool))
                (Sset _t'2 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'2 tint)
                (Ssequence
                  (Sset _child
                    (Ebinop Oadd (Etempvar _child (tptr tint))
                      (Econst_int (Int.repr 1) tint) (tptr tint)))
                  (Sset _child_i
                    (Ebinop Oadd (Etempvar _child_i tulong)
                      (Econst_int (Int.repr 1) tint) tulong)))
                Sskip))
            (Ssequence
              (Sset _par
                (Ebinop Oadd (Etempvar _base (tptr tint))
                  (Etempvar _par_i tulong) (tptr tint)))
              (Sassign (Ederef (Etempvar _par (tptr tint)) tint)
                (Ederef (Etempvar _child (tptr tint)) tint))))))
      (Sset _par_i (Etempvar _child_i tulong))))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _child_i (Etempvar _par_i tulong))
        (Ssequence
          (Sset _par_i
            (Ebinop Odiv (Etempvar _child_i tulong)
              (Econst_int (Int.repr 2) tint) tulong))
          (Ssequence
            (Sset _child
              (Ebinop Oadd (Etempvar _base (tptr tint))
                (Etempvar _child_i tulong) (tptr tint)))
            (Ssequence
              (Sset _par
                (Ebinop Oadd (Etempvar _base (tptr tint))
                  (Etempvar _par_i tulong) (tptr tint)))
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _child_i tulong)
                                 (Econst_int (Int.repr 1) tint) tint)
                    (Sset _t'3 (Econst_int (Int.repr 1) tint))
                    (Sset _t'3
                      (Ecast
                        (Ebinop Olt (Etempvar _k tint)
                          (Ederef (Etempvar _par (tptr tint)) tint) tint)
                        tbool)))
                  (Sifthenelse (Etempvar _t'3 tint)
                    (Ssequence
                      (Sassign (Ederef (Etempvar _child (tptr tint)) tint)
                        (Etempvar _k tint))
                      Sbreak)
                    Sskip))
                (Sassign (Ederef (Etempvar _child (tptr tint)) tint)
                  (Ederef (Etempvar _par (tptr tint)) tint))))))))
    Sskip))
|}.

Definition f_heapsort := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_vbase, (tptr tint)) :: (_nmemb, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_base, (tptr tint)) :: (_l, tulong) :: (_k, tint) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _nmemb tulong)
                 (Econst_int (Int.repr 1) tint) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Sset _base
      (Ebinop Osub (Etempvar _vbase (tptr tint))
        (Econst_int (Int.repr 1) tint) (tptr tint)))
    (Ssequence
      (Ssequence
        (Sset _l
          (Ebinop Oadd
            (Ebinop Odiv (Etempvar _nmemb tulong)
              (Econst_int (Int.repr 2) tint) tulong)
            (Econst_int (Int.repr 1) tint) tulong))
        (Sloop
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'1
                  (Ecast
                    (Ebinop Osub (Etempvar _l tulong)
                      (Econst_int (Int.repr 1) tint) tulong) tulong))
                (Sset _l (Etempvar _t'1 tulong)))
              (Sifthenelse (Etempvar _t'1 tulong) Sskip Sbreak))
            (Scall None
              (Evar _create (Tfunction
                              (Tcons (tptr tint)
                                (Tcons tulong (Tcons tulong Tnil))) tvoid
                              cc_default))
              ((Etempvar _base (tptr tint)) :: (Etempvar _nmemb tulong) ::
               (Etempvar _l tulong) :: nil)))
          Sskip))
      (Swhile
        (Ebinop Ogt (Etempvar _nmemb tulong) (Econst_int (Int.repr 1) tint)
          tint)
        (Ssequence
          (Sset _k
            (Ederef
              (Ebinop Oadd (Etempvar _base (tptr tint))
                (Etempvar _nmemb tulong) (tptr tint)) tint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _base (tptr tint))
                  (Etempvar _nmemb tulong) (tptr tint)) tint)
              (Ederef
                (Ebinop Oadd (Etempvar _base (tptr tint))
                  (Econst_int (Int.repr 1) tint) (tptr tint)) tint))
            (Ssequence
              (Sset _nmemb
                (Ebinop Osub (Etempvar _nmemb tulong)
                  (Econst_int (Int.repr 1) tint) tulong))
              (Scall None
                (Evar _heapify (Tfunction
                                 (Tcons (tptr tint)
                                   (Tcons tulong (Tcons tint Tnil))) tvoid
                                 cc_default))
                ((Etempvar _base (tptr tint)) :: (Etempvar _nmemb tulong) ::
                 (Etempvar _k tint) :: nil)))))))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_create, Gfun(Internal f_create)) ::
 (_heapify, Gfun(Internal f_heapify)) ::
 (_heapsort, Gfun(Internal f_heapsort)) :: nil).

Definition public_idents : list ident :=
(_heapsort :: _heapify :: _create :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


