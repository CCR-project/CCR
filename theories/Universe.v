Class Universe := {
  syscall: Type;
  val: Type;
}
.

Context `{Universe}.

Inductive event: Type :=
| event_sys
    (sys: syscall)
| event_exit (rv: val)
(* | event_tau *)
| event_ub
| event_nb
.

(* Coercion event_sys: syscall >-> event. *)
