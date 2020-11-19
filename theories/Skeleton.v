From Paco Require Import paco.
Require Import Program.
Require Import sflib.
Require Import Universe.
Require Import STS.
Require Import Behavior.

Set Implicit Arguments.


Module Sk.

  Definition t: Type := admit "".

End Sk.



Module SkEnv.

  Definition t: Type := admit "".

  Definition project: t -> Sk.t -> t := admit "".

End SkEnv.
