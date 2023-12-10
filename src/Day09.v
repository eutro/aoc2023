From Coq Require Export String List ZArith.
From Coq Require Import Lia Program.Wf.

Export ListNotations.

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

Lemma cons_length {A : Type} : forall (x : A) (xs : list A), List.length (x :: xs) = S (List.length xs).
Proof. intros x xs. unfold length. reflexivity. Qed.
Lemma tl_length {A : Type} : forall (xs : list A), List.length (tl xs) = pred (List.length xs).
Proof.
  intros xs.
  unfold tl.
  destruct xs as [ | _h xtl ].
  - reflexivity.
  - rewrite cons_length, Nat.pred_succ.
    reflexivity.
Qed.

Lemma list_der_length: forall xs, List.length (list_der xs) = pred (List.length xs).
Proof.
  intros xs.
  unfold list_der, list_diff.
  rewrite map_length, combine_length, tl_length.
  set (len := List.length xs).
  refine (min_r len (pred len) _).
  unfold pred.
  destruct len.
  - reflexivity.
  - apply Peano.le_S.
    reflexivity.
Qed.

Program Fixpoint step_seq_ (xs : list Z) {measure (List.length xs)} : Z :=
  if List.forallb (Z.eqb 0) xs then 0 else
    match xs with
    | [] => 0
    | h::_ => h + (step_seq_ (list_der xs))
    end.
Obligation 1.
Proof.
  rewrite list_der_length.
  unfold length.
  rewrite Nat.pred_succ.
  unfold Peano.lt.
  reflexivity.
Qed.

Definition step_seq_back (xs : list Z) : Z := step_seq_ xs.
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
