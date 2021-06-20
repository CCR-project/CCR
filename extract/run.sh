sed -i 's/let sort : Coq__Order.t list -> Coq__Order.t list/let sort/' AList.ml &&
sed -i 's/let sort/let sort : Coq__Order.t list -> Coq__Order.t list/' AList.ml &&
ocamlbuild main.native && ./main.native
