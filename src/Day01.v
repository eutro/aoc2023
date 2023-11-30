From Coq Require Export List NArith.
From Coq Require Import Arith Sorting Orders OrdersEx Lia.

Import ListNotations.

#[global] Open Scope N_scope.

Module NTotalOrder := OTF_to_TTLB N_as_OT. 
Module SortN := Sort NTotalOrder.

Declare Custom Entry grouping.
Notation "'input' line ',' .. ',' lines" := (cons line .. (cons lines nil) ..)
                               (at level 200, line custom grouping, only parsing).
Notation "x .. xs" := (cons x .. (cons xs nil) ..)
                        (in custom grouping at level 1, x constr at level 0).

Definition example : list (list N) := input
1000
2000
3000
,
4000
,
5000
6000
,
7000
8000
9000
,
10000
.

Fixpoint sum_ns_ (xs : list N) (acc : N) : N :=
  match xs with
  | [] => acc
  | x :: tl => sum_ns_ tl (acc + x)
  end.

Fixpoint take (n : nat) (xs : list N) : list N :=
  match n, xs with
  | O, _ | _, [] => []
  | S m, x :: tl => x :: take m tl
  end.

Definition sum_ns (xs : list N) : N := sum_ns_ xs 0.

Definition main (xs : list (list N)) : (N * N) :=
  let totals := map sum_ns xs in
  let sorted := rev (SortN.sort totals) in
  (nth 0 sorted 0,
    sum_ns (take 3 sorted)).
