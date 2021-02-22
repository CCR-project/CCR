#include "stdio.h"
#include "stdlib.h"

//// preliminary

/*
In order to define the "is_list" predicate conveniently, we define the following syntactic sugar (following Iris).

```
  (*** Σ is type of the global resource ***)
  Definition iProp := Σ -> Prop.
  Definition sepconj (P Q: iProp): iProp := fun r => exists a b, r = URA.add a b /\ P a /\ Q b.
  Definition Pure (P: Prop): iProp := fun _ => P.
  Definition Ex {X: Type} (P: X -> iProp): iProp := fun r => exists x, P x r.

  Infix "**" := sepconj (at level 60).
  Notation "'⌜' P '⌝'" := (Pure P).
  Notation "'Exists' x .. y , p" := (Ex (fun x => .. (Ex (fun y => p)) ..)).

  Fixpoint is_list (ll: val) (xs: list nat): iProp :=
    match xs with
    | [] => ⌜ll = Vnullptr⌝
    | xhd :: xtl => Exists ltl, ((ll,0) |-> (xhd, ltl)) ** is_list ltl xtl
    end
  .
```
*/


/*
(Type of the pre/post conditions)
Consider the following standard Hoare triple.
```forall (x: X), {{ precond }} ret := f(arg) {{ postcond }}```

------>

In our framework, it is expressed like this:
```
Record fspec: Type := mk {
  X: Type; (*** a meta-variable ***)
  precond: X -> Any.t -> iProp;  (*** meta-variable -> physical arg -> ghost resource arg -> Prop ***)
  postcond: X -> Any.t -> iProp; (*** meta-variable -> physical ret -> ghost resource ret -> Prop ***)
}.
```

Actually, our framework is slightly more complicated because of the following features.
- We have "measure" for termination proof.
- We support "high-level logical arg/ret". (not used in this example, so ignore this at the moment)

Actual "fspec" directly copied from Coq code:
```
Record fspec: Type := mk {
  X: Type; (*** a meta-variable ***)
  precond: X -> Any.t -> Any.t -> iProp;  (*** meta-variable -> high-level logical arg -> low-level logical arg (== physical arg) -> ghost resource arg -> Prop ***)
  postcond: X -> Any.t -> Any.t -> iProp; (*** meta-variable -> high-level logical ret -> low-level logical ret (== physical ret) -> ghost resource ret -> Prop ***)
  measure: X -> option Ordinal.t;
}.
```
*/










//// linked list

struct Node {
  int val;
  struct Node* next;
};

/*
forall (xs: list nat) (x: nat), {{ is_list ll xs ** ⌜n = Vint (Z.of_nat x)⌝}} r := push(ll, n) {{ is_list r (x :: xs) }}
body := (Choose _)
*/
struct Node* push(struct Node* ll, int n) {
  struct Node* new_node = malloc(sizeof(struct Node));
  new_node->val = n;
  new_node->next = ll;
  return new_node;
}

/*
forall ll xs, {{ (llref,0) |-> ll ** is_list ll xs}} r := pop(ll)
              {{ match xs with
                 | [] => ⌜r = Vint -1⌝
                 | xhd :: xtl => ⌜r = Vint (Z.of_nat xhd)⌝ ** (Exists ll', (llref,0) |-> ll' ** is_list ll' xtl)
                 end
              }}
body := (Choose _)
*/
int pop(struct Node** llref) {
  if(*llref) {
    int v = (*llref)->val;
    struct Node* next = (*llref)->next;
    free(*llref);
    (*llref) = next;
    return v;
  }
  return -1;
}











//// client
int in() {
  int n;
  scanf("%d", &n);
  return n;
}

void out(int n) {
  printf("%d\t", n);
}










//// echo
/*
  module-local logical state ----> xs: list nat
  module-local ghost   state ----> mr: Σ
  echo <= echo_spec invariant ---> (is_list my_list xs) mr
 */
struct Node* my_list = NULL;

void echo_finish();
/*
{{ }} r := echo() {{ }}
body := n <- (Call in []);;
        if(n == -1)
        then (Call echo_finish [])
        else (
          xs <- LGet;;
          ARBITRARY_PURE_CALLS;; //(Call push [my_list; n]);;
          LPut (x :: xs);;
          (Call echo [])
        )
 */
void echo() {
  int n = in();
  if(n == -1) {
    echo_finish();
    return;
  }
  my_list = push(my_list, n);
  echo();
}

/*
{{ }} r := echo_finish() {{ }}
body := xs <- LGet;;
        ARBITRARY_PURE_CALLS;; //(Call pop [my_list]);;
        match xs with
        | []  => Ret tt
        | xhd :: xtl =>
          (Call out [Vint (Z.of_nat xhd)]);;
          (Call echo_finish [])
        end
 */
void echo_finish() {
  int n = pop(&my_list);
  if(n == -1) return;
  else {
    out(n);
    echo_finish();
  }
}

int main() {
  echo();
}
