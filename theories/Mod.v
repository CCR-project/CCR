From Paco Require Import paco.
Require Import Program.
Require Import sflib.
Require Import Universe.
Require Import Sem.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.

Set Implicit Arguments.



(* Module Mod. *)

(*   Record t: Type := mk { *)
(*     sk: Sk.t; *)
(*     get_modsem: SkEnv.t -> ModSemL.t; *)
(*     name: string; *)
(*     get_modsem_skenv: forall skenv_link, *)
(*         <<PROJ: SkEnv.project skenv_link sk = (get_modsem skenv_link).(ModSemL.skenv)>>; *)
(*     get_modsem_name: forall skenv_link, *)
(*         <<PROJ: name = (get_modsem skenv_link).(ModSemL.name)>>; *)
(*   } *)
(*   . *)

(* End Mod. *)
