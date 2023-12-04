From Coq Require Export String List NArith.
From Coq Require Import Lia Ascii Sorting Orders OrdersEx.

Import ListNotations.

#[global] Open Scope nat_scope.
#[global] Open Scope N_scope.

Module N_TTLB := OTF_to_TTLB N.
Module SortN := Sort N_TTLB.

Inductive card : Set :=
| CardOf : N -> list N -> list N -> card.

Declare Custom Entry card.
Declare Custom Entry side.
Notation "'input' card .. cards" :=
  (cons card .. (cons cards nil) ..)
    (at level 200, card custom card at level 3, only parsing).
Notation "'Card' n ':' side1 '|' side2" :=
  (CardOf n side1 side2)
    (in custom card at level 2,
        n constr at level 0,
        side1 custom side at level 1,
        side2 custom side at level 1).
Notation "n .. ns" :=
  (cons n .. (cons ns nil) ..)
    (in custom side at level 1, n constr at level 0).

Fixpoint nat_map {A : Type} (s : A -> A) (o : A) (n : nat) :=
  match n with O => o | S m => nat_map s (s o) m end.

Fixpoint score_card_ (c : nat) (acc : nat) (whs : list N * list N) : nat :=
  match (whs, c) with
  | (w::wtl, h::htl, S m) =>
      match N.compare w h with
      | Eq => score_card_ m (S acc) (wtl, htl)
      | Lt => score_card_ m acc (wtl, h::htl)
      | Gt => score_card_ m acc (w::wtl, htl)
      end
  | ([], _, _) | (_, [], _) | (_, _, O) => acc
  end.
Definition score_card (c : card) : nat :=
  let 'CardOf _ winning had := c in
  score_card_ (length winning + length had) O
    (SortN.sort winning, SortN.sort had).

Definition succ_winning (n : N) : N := match n with 0 => 1 | _ => 2 * n end.
Definition get_score s := nat_map succ_winning 0 s.
Definition card_points c := get_score (score_card c).

Fixpoint add_mults (mult : N) (n : nat) (l : list N) : list N :=
  match n with
  | O => l
  | S m => (mult + hd 0 l) :: add_mults mult m (tl l)
  end.
Fixpoint count_cards (acc : N) (mults : list N) (matches : list nat) : N :=
  match matches with
  | [] => acc
  | ms :: mtl =>
      let multiplier := 1 + hd 0 mults in
      let mults' := add_mults multiplier ms (tl mults) in
      count_cards (acc + multiplier) mults' mtl
  end.

Definition part1 (scores : list nat) := fold_left N.add (map get_score scores) 0.
Definition part2 (scores : list nat) := count_cards 0 [] scores.
Definition main (cs : list card) :=
  let scores := map score_card cs in
  (part1 scores, part2 scores).

Definition example := input
Card 1: 41 48 83 86 17 | 83 86  6 31 17  9 48 53
Card 2: 13 32 20 16 61 | 61 30 68 82 17 32 24 19
Card 3:  1 21 53 59 44 | 69 82 63 72 16 21 14  1
Card 4: 41 92 73 84 69 | 59 84 76 51 58  5 54 83
Card 5: 87 83 26 28 32 | 88 30 70 12 93 22 82 36
Card 6: 31 18 13 56 72 | 74 77 10 23 35 67 36 11
.

Definition example_scores := map score_card example.
Example example_counts: example_scores = [4; 2; 2; 1; 0; 0]%nat.
Proof. simpl. reflexivity. Qed.

Example example_part1: part1 example_scores = 13.
Proof. simpl. reflexivity. Qed.
Example example_part2: part2 example_scores = 30.
Proof. simpl. reflexivity. Qed.
