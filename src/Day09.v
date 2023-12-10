From Coq Require Export String List ZArith.
From Coq Require Import Lia Ascii Sorting Orders OrdersEx OrdersAlt Init.Byte.

Export ListNotations.
Import IfNotations.

#[global] Open Scope Z_scope.

Declare Custom Entry history.
Declare Custom Entry integer.
Notation "'input' line .. lines" :=
  (cons line .. (cons lines nil) ..)
    (at level 200, line custom history at level 2, only parsing).
Notation "entry .. entries ';'" :=
  (cons entry .. (cons entries nil) ..)
    (in custom history at level 2, entry custom integer at level 1).
Notation "'-' n" := (- n) (in custom integer at level 1, n constr at level 0).
Notation "n" := n (in custom integer at level 0, n constr at level 0).

Definition list_diff (xs ys : list Z) : list Z :=
  List.map (fun '(x, y) => x - y) (List.combine xs ys).
Definition list_der (xs : list Z) : list Z := list_diff xs (tl xs).

Fixpoint step_seq_ (len : nat) (xs : list Z) : Z :=
  if List.forallb (Z.eqb 0) xs then 0 else
    match len with
    | O => 0
    | S len' => List.hd 0 xs + (step_seq_ len' (list_der xs))
    end.
Definition step_seq_back (xs : list Z) : Z := step_seq_ (List.length xs) xs.
Definition step_seq (xs : list Z) : Z := step_seq_back (List.rev xs).

Definition part (f : list Z -> Z) (inp : list (list Z)) :=
  let next_terms := List.map f inp in
  List.fold_left Z.add next_terms 0.
Definition main (inp : list (list Z)) :=
  (part step_seq inp, part step_seq_back inp).

Definition example := input
0 3 6 9 12 15;
1 3 6 10 15 21;
10 13 16 21 30 45;
.

Example sample_input: main example = (114, 2).
Proof. reflexivity. Qed.
