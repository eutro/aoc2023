From Coq Require Import Lia Orders OrdersAlt.

Module Type Mapper (Src Dst : Typ).
  Parameter map : Src.t -> Dst.t.
End Mapper.

Module OrderByFun (Src : Typ) (Dst : OrderedTypeAlt) (M : Mapper Src Dst).
  Definition t : Type := Src.t.

  Definition compare (l r : t) : comparison :=
    Dst.compare (M.map l) (M.map r).

  Infix "?=" := compare (at level 70, no associativity).

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof. intros x y. apply Dst.compare_sym. Qed.
  Lemma compare_trans : forall c x y z, (x ?= y) = c -> (y ?= z) = c -> (x ?= z) = c.
  Proof. intros c x y z. apply Dst.compare_trans. Qed.
End OrderByFun.
