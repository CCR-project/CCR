open AST
open Archi
open BinInt
open BinNums
open Cop
open Coqlib
open Csyntax
open Ctypes
open Datatypes
open Errors
open Integers
open List0
open Maps
open Memory
open Values

(** val do_cast : coq_val -> coq_type -> coq_type -> coq_val res **)

let do_cast v t1 t2 =
  match sem_cast v t1 t2 Mem.empty with
  | Some v' -> OK v'
  | None ->
    Error
      (msg
        ('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('c'::('a'::('s'::('t'::[])))))))))))))))

(** val lookup_composite : composite_env -> ident -> composite res **)

let lookup_composite ce id =
  match PTree.get id ce with
  | Some co -> OK co
  | None ->
    Error ((MSG
      ('U'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('s'::('t'::('r'::('u'::('c'::('t'::(' '::('o'::('r'::(' '::('u'::('n'::('i'::('o'::('n'::(' '::[]))))))))))))))))))))))))))) :: ((CTX
      id) :: []))

(** val constval : composite_env -> expr -> coq_val res **)

let rec constval ce = function
| Eval (v, _) ->
  (match v with
   | Vundef ->
     Error
       (msg
         ('i'::('l'::('l'::('e'::('g'::('a'::('l'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::[])))))))))))))))))
   | Vptr (_, _) ->
     Error
       (msg
         ('i'::('l'::('l'::('e'::('g'::('a'::('l'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::[])))))))))))))))))
   | _ -> OK v)
| Evar (x, _) -> OK (Vptr (x, Ptrofs.zero))
| Efield (l, f, _) ->
  (match typeof l with
   | Tstruct (id, _) ->
     (match lookup_composite ce id with
      | OK x ->
        (match field_offset ce f x.co_members with
         | OK x0 ->
           (match constval ce l with
            | OK x1 ->
              OK
                (if ptr64
                 then Val.addl x1 (Vlong (Int64.repr x0))
                 else Val.add x1 (Vint (Int.repr x0)))
            | Error msg0 -> Error msg0)
         | Error msg0 -> Error msg0)
      | Error msg0 -> Error msg0)
   | Tunion (_, _) -> constval ce l
   | _ ->
     Error
       (msg
         ('i'::('l'::('l'::('-'::('t'::('y'::('p'::('e'::('d'::(' '::('f'::('i'::('e'::('l'::('d'::(' '::('a'::('c'::('c'::('e'::('s'::('s'::[]))))))))))))))))))))))))
| Evalof (l, ty) ->
  (match access_mode ty with
   | By_value _ ->
     Error
       (msg
         ('d'::('e'::('r'::('e'::('f'::('e'::('r'::('e'::('n'::('c'::('i'::('n'::('g'::(' '::('o'::('f'::(' '::('a'::('n'::(' '::('l'::('-'::('v'::('a'::('l'::('u'::('e'::[]))))))))))))))))))))))))))))
   | By_nothing ->
     Error
       (msg
         ('d'::('e'::('r'::('e'::('f'::('e'::('r'::('e'::('n'::('c'::('i'::('n'::('g'::(' '::('o'::('f'::(' '::('a'::('n'::(' '::('l'::('-'::('v'::('a'::('l'::('u'::('e'::[]))))))))))))))))))))))))))))
   | _ -> constval ce l)
| Ederef (r, _) -> constval ce r
| Eaddrof (l, _) -> constval ce l
| Eunop (op, r1, _) ->
  (match constval ce r1 with
   | OK x ->
     (match sem_unary_operation op x (typeof r1) Mem.empty with
      | Some v -> OK v
      | None ->
        Error
          (msg
            ('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('u'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))
   | Error msg0 -> Error msg0)
| Ebinop (op, r1, r2, _) ->
  (match constval ce r1 with
   | OK x ->
     (match constval ce r2 with
      | OK x0 ->
        (match sem_binary_operation ce op x (typeof r1) x0 (typeof r2)
                 Mem.empty with
         | Some v -> OK v
         | None ->
           Error
             (msg
               ('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Ecast (r, ty) ->
  (match constval ce r with
   | OK x -> do_cast x (typeof r) ty
   | Error msg0 -> Error msg0)
| Eseqand (r1, r2, _) ->
  (match constval ce r1 with
   | OK x ->
     (match constval ce r2 with
      | OK x0 ->
        (match bool_val x (typeof r1) Mem.empty with
         | Some b ->
           if b then do_cast x0 (typeof r2) type_bool else OK (Vint Int.zero)
         | None ->
           Error
             (msg
               ('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('&'::('&'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Eseqor (r1, r2, _) ->
  (match constval ce r1 with
   | OK x ->
     (match constval ce r2 with
      | OK x0 ->
        (match bool_val x (typeof r1) Mem.empty with
         | Some b ->
           if b then OK (Vint Int.one) else do_cast x0 (typeof r2) type_bool
         | None ->
           Error
             (msg
               ('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('|'::('|'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Econdition (r1, r2, r3, ty) ->
  (match constval ce r1 with
   | OK x ->
     (match constval ce r2 with
      | OK x0 ->
        (match constval ce r3 with
         | OK x1 ->
           (match bool_val x (typeof r1) Mem.empty with
            | Some b ->
              if b
              then do_cast x0 (typeof r2) ty
              else do_cast x1 (typeof r3) ty
            | None ->
              Error
                (msg
                  ('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::[]))))))))))))))))))))))))
         | Error msg0 -> Error msg0)
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Esizeof (ty1, _) -> OK (coq_Vptrofs (Ptrofs.repr (sizeof ce ty1)))
| Ealignof (ty1, _) -> OK (coq_Vptrofs (Ptrofs.repr (alignof ce ty1)))
| Ecomma (r1, r2, _) ->
  (match constval ce r1 with
   | OK _ -> constval ce r2
   | Error msg0 -> Error msg0)
| Eparen (r, tycast, _) ->
  (match constval ce r with
   | OK x -> do_cast x (typeof r) tycast
   | Error msg0 -> Error msg0)
| _ ->
  Error
    (msg
      ('n'::('o'::('t'::(' '::('a'::(' '::('c'::('o'::('m'::('p'::('i'::('l'::('e'::('-'::('t'::('i'::('m'::('e'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::[]))))))))))))))))))))))))))))

(** val constval_cast : composite_env -> expr -> coq_type -> coq_val res **)

let constval_cast ce a ty =
  match constval ce a with
  | OK x -> do_cast x (typeof a) ty
  | Error msg0 -> Error msg0

type coq_initializer =
| Init_single of expr
| Init_array of initializer_list
| Init_struct of initializer_list
| Init_union of ident * coq_initializer
and initializer_list =
| Init_nil
| Init_cons of coq_initializer * initializer_list

(** val transl_init_single :
    composite_env -> coq_type -> expr -> init_data res **)

let transl_init_single ce ty a =
  match constval_cast ce a ty with
  | OK x ->
    (match x with
     | Vundef ->
       Error
         (msg
           ('u'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))))))))))))))))))))))))))
     | Vint n ->
       (match ty with
        | Tint (i, _, _) ->
          (match i with
           | I16 -> OK (Init_int16 n)
           | I32 -> OK (Init_int32 n)
           | _ -> OK (Init_int8 n))
        | Tpointer (_, _) ->
          if negb ptr64 then OK (Init_int32 n) else assertion_failed
        | _ ->
          Error
            (msg
              ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))
     | Vlong n ->
       (match ty with
        | Tlong (_, _) -> OK (Init_int64 n)
        | Tpointer (_, _) ->
          if ptr64 then OK (Init_int64 n) else assertion_failed
        | _ ->
          Error
            (msg
              ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))
     | Vfloat f ->
       (match ty with
        | Tfloat (f0, _) ->
          (match f0 with
           | F32 ->
             Error
               (msg
                 ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))))))))))))))))))))
           | F64 -> OK (Init_float64 f))
        | _ ->
          Error
            (msg
              ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))
     | Vsingle f ->
       (match ty with
        | Tfloat (f0, _) ->
          (match f0 with
           | F32 -> OK (Init_float32 f)
           | F64 ->
             Error
               (msg
                 ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))
        | _ ->
          Error
            (msg
              ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))
     | Vptr (id, ofs) ->
       (match ty with
        | Tint (i, _, _) ->
          (match i with
           | I32 ->
             if negb ptr64
             then OK (Init_addrof (id, ofs))
             else assertion_failed
           | _ ->
             Error
               (msg
                 ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))
        | Tlong (_, _) ->
          if ptr64 then OK (Init_addrof (id, ofs)) else assertion_failed
        | Tpointer (_, _) -> OK (Init_addrof (id, ofs))
        | _ ->
          Error
            (msg
              ('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))))))))))))))))))))))
  | Error msg0 -> Error msg0

(** val padding : coq_Z -> coq_Z -> init_data list -> init_data list **)

let padding frm to0 k =
  if zlt frm to0 then (Init_space (Z.sub to0 frm)) :: k else k

(** val transl_init_rec :
    composite_env -> coq_type -> coq_initializer -> init_data list ->
    init_data list res **)

let rec transl_init_rec ce ty i k =
  match i with
  | Init_single a ->
    (match transl_init_single ce ty a with
     | OK x -> OK (x :: k)
     | Error msg0 -> Error msg0)
  | Init_array il ->
    (match ty with
     | Tarray (tyelt, nelt, _) ->
       transl_init_array ce tyelt il (Z.max Z0 nelt) k
     | _ ->
       Error
         (msg
           ('w'::('r'::('o'::('n'::('g'::(' '::('t'::('y'::('p'::('e'::(' '::('f'::('o'::('r'::(' '::('c'::('o'::('m'::('p'::('o'::('u'::('n'::('d'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))))))))))))))))))))))))))))
  | Init_struct il ->
    (match ty with
     | Tstruct (id, _) ->
       (match lookup_composite ce id with
        | OK x ->
          (match x.co_su with
           | Struct -> transl_init_struct ce ty x.co_members il Z0 k
           | Union ->
             Error ((MSG
               ('s'::('t'::('r'::('u'::('c'::('t'::('/'::('u'::('n'::('i'::('o'::('n'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('o'::('n'::(' '::[])))))))))))))))))))))))))) :: ((CTX
               id) :: [])))
        | Error msg0 -> Error msg0)
     | _ ->
       Error
         (msg
           ('w'::('r'::('o'::('n'::('g'::(' '::('t'::('y'::('p'::('e'::(' '::('f'::('o'::('r'::(' '::('c'::('o'::('m'::('p'::('o'::('u'::('n'::('d'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))))))))))))))))))))))))))))
  | Init_union (f, i1) ->
    (match ty with
     | Tunion (id, _) ->
       (match lookup_composite ce id with
        | OK x ->
          (match x.co_su with
           | Struct ->
             Error ((MSG
               ('u'::('n'::('i'::('o'::('n'::('/'::('s'::('t'::('r'::('u'::('c'::('t'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('o'::('n'::(' '::[])))))))))))))))))))))))))) :: ((CTX
               id) :: []))
           | Union ->
             (match field_type f x.co_members with
              | OK x0 ->
                (match transl_init_rec ce x0 i1 k with
                 | OK x1 -> OK (padding (sizeof ce x0) (sizeof ce ty) x1)
                 | Error msg0 -> Error msg0)
              | Error msg0 -> Error msg0))
        | Error msg0 -> Error msg0)
     | _ ->
       Error
         (msg
           ('w'::('r'::('o'::('n'::('g'::(' '::('t'::('y'::('p'::('e'::(' '::('f'::('o'::('r'::(' '::('c'::('o'::('m'::('p'::('o'::('u'::('n'::('d'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))))))))))))))))))))))))))))

(** val transl_init_array :
    composite_env -> coq_type -> initializer_list -> coq_Z -> init_data list
    -> init_data list res **)

and transl_init_array ce ty il sz k =
  match il with
  | Init_nil ->
    if zeq sz Z0
    then OK k
    else if zle Z0 sz
         then OK ((Init_space (Z.mul sz (sizeof ce ty))) :: k)
         else Error
                (msg
                  ('w'::('r'::('o'::('n'::('g'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('e'::('l'::('e'::('m'::('e'::('n'::('t'::('s'::(' '::('i'::('n'::(' '::('a'::('r'::('r'::('a'::('y'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))))))))))))
  | Init_cons (i1, il') ->
    (match transl_init_rec ce ty i1 k with
     | OK x -> transl_init_array ce ty il' (Z.sub sz (Zpos Coq_xH)) x
     | Error msg0 -> Error msg0)

(** val transl_init_struct :
    composite_env -> coq_type -> members -> initializer_list -> coq_Z ->
    init_data list -> init_data list res **)

and transl_init_struct ce ty fl il pos k =
  match il with
  | Init_nil ->
    (match fl with
     | [] -> OK (padding pos (sizeof ce ty) k)
     | _ :: _ ->
       Error
         (msg
           ('w'::('r'::('o'::('n'::('g'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('e'::('l'::('e'::('m'::('e'::('n'::('t'::('s'::(' '::('i'::('n'::(' '::('s'::('t'::('r'::('u'::('c'::('t'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))))))))))))))
  | Init_cons (i1, il') ->
    (match fl with
     | [] ->
       Error
         (msg
           ('w'::('r'::('o'::('n'::('g'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('e'::('l'::('e'::('m'::('e'::('n'::('t'::('s'::(' '::('i'::('n'::(' '::('s'::('t'::('r'::('u'::('c'::('t'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))))))))))))))))))))))))))))))))))))))
     | p :: fl' ->
       let (_, ty1) = p in
       let pos1 = align pos (alignof ce ty1) in
       (match transl_init_rec ce ty1 i1 (padding pos pos1 k) with
        | OK x ->
          transl_init_struct ce ty fl' il' (Z.add pos1 (sizeof ce ty1)) x
        | Error msg0 -> Error msg0))

(** val transl_init :
    composite_env -> coq_type -> coq_initializer -> init_data list res **)

let transl_init ce ty i =
  match transl_init_rec ce ty i [] with
  | OK x -> OK (rev' x)
  | Error msg0 -> Error msg0
