From Coq Require Export String List NArith.
From Coq Require Import Lia Ascii Sorting Orders OrdersEx.

Export ListNotations.

#[global] Open Scope N_scope.

Notation "'input' 'Time' ':' time .. times 'Distance' ':' dist .. dists" :=
  (combine
     (cons time .. (cons times nil) ..)
     (cons dist .. (cons dists nil) ..))
    (at level 200, time at level 0, dist at level 0).

Definition race_time (duration hold : N) : N := (duration - hold) * hold.

Definition best_race_hold (duration : N) : N := duration / 2.

Definition halve_floor (x : N) : N := x / 2.
Definition halve_ceil (x : N) : N := x - x / 2.
Definition race_bounds (duration target : N) : N * N :=
  (* solve (duration - x) * x > target
   => -x^2 + duration * x - target > 0
   => -(x - duration/2)^2 + duration^2/4 - target > 0
   => (x - duration/2)^2 < duration^2/4 - target
   => x - duration/2 ∈ (±,sqrt(duration^2/4 - target))
   => x ∈ (duration/2 ±, sqrt(duration^2/4 - target))
   => 2x ∈ (duration ±, sqrt(duration^2 - 4target)) *)
  (* we use target + 1 and >= instead *)
  let det := N.square duration - 4 * (target + 1) in
  let sqrt_det (* lower bound of sqrt *) := N.sqrt det in
  let '(mn2, mx2) := (duration - sqrt_det, duration + sqrt_det) in
  (halve_ceil mn2, halve_floor mx2).

Definition race_cways (race : N * N) : N :=
  let '(time, dist) := race in
  let '(mn, mx) := race_bounds time dist in
  mx + 1 - mn.
Definition races_cways (races : list (N * N)) := List.map race_cways races.

Fixpoint combine_dec_ (c : nat) (lhs rhs : N) : N :=
  match c with
  | O => lhs
  | S m =>
      if rhs =? 0 then lhs
      else (combine_dec_ m lhs (rhs / 10)) * 10 + (rhs mod 10)
  end.
Definition combine_dec (lhs rhs : N) : N :=
  combine_dec_ (N.to_nat rhs) lhs rhs.

Definition combine_races (races : list (N * N)) : N * N :=
  List.fold_left
    (fun '(t1, d1) '(t2, d2) =>
       (combine_dec t1 t2, combine_dec d1 d2))
    races (0, 0).
Definition main (races : list (N * N)) :=
  (List.fold_left N.mul (races_cways races) 1,
    race_cways (combine_races races)).

Definition example := input
Time:      7  15   30
Distance:  9  40  200
.

Example example_cways: races_cways example = [4; 8; 9].
Proof. simpl. reflexivity. Qed.
Example example_combined_cways: race_cways (combine_races example) = 71503.
Proof. simpl. reflexivity. Qed.
