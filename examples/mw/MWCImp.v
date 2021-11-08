Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.



Section PROOF.
  Context `{Σ: GRA.t}.

  Import ImpNotations.
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition loopF :=
    mk_function
      []
      []
      (@ "run" [] ;# @ "loop" [])
  .

  Definition mainF :=
    mk_function
      []
      ["arr"; "map"; "tmp"]
      ("tmp" =# malloc# 100%Z ;# "arr" =#& "gv0" ;# "arr" *=# "tmp" ;#
       "tmp" =@ "new" [] ;# "map" =#& "gv1" ;# "map" *=# "tmp" ;#
       @ "init" [] ;#
       @ "loop" []
      )
  .

  Definition putF :=
    mk_function
      ["k"; "v"]
      ["arr"; "arrv"; "map"; "mapv"; "tmp"]
      ((* if# ((0%Z =? "k") + (0%Z <"k")) * ("k" < 100%Z) *)
       if# ((- 1)%Z < "k") * ("k" < 100%Z)
       then# "arr" =#& "gv0" ;# "arrv" =#* "arr" ;# ("arrv" + (8%Z * "k")) *=# "v"
       else# "map" =#& "gv1" ;# "mapv" =#* "map" ;# @ "update" ["map": expr; "k": expr; "v": expr]
       fi# ;#
       @! "print" ["k" : expr] ;#
       @! "print" ["v" : expr]
      )
  .

  Definition getF :=
    mk_function
      ["k"]
      ["v"; "arr"; "map"; "tmp"]
      (if# ((- 1)%Z < "k") * ("k" < 100%Z)
       then# "arr" =#& "gv0" ;# "arrv" =#* "arr" ;# "v" =#* ("arrv" + (8%Z * "k"))
       else# "map" =#& "gv1" ;# "mapv" =#* "map" ;# "v" =@ "access" ["map": expr; "k": expr]
       fi# ;#
       @! "print" ["k" : expr] ;#
       @! "print" ["v" : expr] ;#
       return# "v"
      )
  .
      (* k <- (pargs [Tint] varg)?;; *)
      (* assume(intrange_64 k);;; *)
      (* '(arr, map) <- pget;; *)
      (* `v: val <- (if ((0 <=? k) && (k <? 100))%Z *)
      (*             then ccallU "load" [add_ofs arr k] *)
      (*             else ccallU "access" ([map; Vint k]));; *)
      (* trigger (Syscall "print" [Vint k]↑ top1);;; (*** TODO: make something like "syscallu" ***) *)
      (* trigger (Syscall "print" [v]↑ top1);;; *)
      (* Ret v *)

  Definition MWprog: program :=
    mk_program
      "MW"
      []
      [("init", 0); ("loop", 0); ("new", 0); ("update", 0); ("access", 0)]
      [("gv0", 0%Z); ("gv1", 0%Z); ("gv2", 0%Z); ("gv3", 0%Z)]
      [("main", mainF); ("loop", loopF); ("put", putF); ("get", getF)]
  .

  Definition MWSem ge: ModSem.t := ImpMod.modsem MWprog ge.
  Definition MW: Mod.t := ImpMod.get_mod MWprog.

End PROOF.
