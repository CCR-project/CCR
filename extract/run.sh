#!/bin/bash
perl -i -pe's/let sort : Coq__Order.t list -> Coq__Order.t list/let sort/g' AList.ml &&
  perl -i -pe's/let sort/let sort : Coq__Order.t list -> Coq__Order.t list/g' AList.ml &&
  #sed works in linux but not OS X
#sed -i 's/let sort : Coq__Order.t list -> Coq__Order.t list/let sort/' AList.ml &&
#sed -i 's/let sort/let sort : Coq__Order.t list -> Coq__Order.t list/' AList.ml &&
ocamlbuild main.native && ./main.native
