Class Universe := {
  syscall: Type;
  val: Type;
}
.

Context `{Universe}.

Inductive event: Type :=
| event_sys
    (sys: syscall)
(* | event_tau *)
.

(* Coercion event_sys: syscall >-> event. *)
