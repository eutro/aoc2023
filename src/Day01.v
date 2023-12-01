From Coq Require Export String List NArith.
From Coq Require Import Lia.

Import ListNotations.
Import StringSyntax.

#[global] Open Scope N_scope.
#[global] Open Scope string_scope.

Notation "'input' line .. lines" :=
  (cons line .. (cons lines nil) ..)
    (at level 200, line at level 0, only parsing).

Definition rev_s (s : string) : string :=
  string_of_list_ascii (rev (list_ascii_of_string s)).

Definition digit_map :=
  [("0", 0); ("1", 1); ("2", 2); ("3", 3); ("4", 4);
   ("5", 5); ("6", 6); ("7", 7); ("8", 8); ("9", 9)].

Definition digit_map2 :=
  rev_append digit_map
    [("one", 1); ("two", 2); ("three", 3); ("four", 4); ("five", 5);
     ("six", 6); ("seven", 7); ("eight", 8); ("nine", 9)].

Definition rev_dmap (l : list (string * N)) : list (string * N) :=
  map (fun '(s, n) => (rev_s s, n)) l.

Fixpoint prefix_assoc (l : list (string * N)) (s : string) : option N :=
  match l with
  | [] => None
  | (pref, digit) :: tl =>
      if prefix pref s
      then Some digit
      else prefix_assoc tl s
  end.

Definition peek_digit (dmap : list (string * N)) (s : string) : option N :=
  prefix_assoc dmap s.
Fixpoint find_digit (dmap : list (string * N)) (s : string) : N :=
  match peek_digit dmap s with
  | Some d => d
  | None =>
      (match s with
       | EmptyString => 0
       | String _ tl => find_digit dmap tl
      end)
  end.

Definition cval (dmap : list (string * N)) (s : string) : N :=
  let d1 := find_digit dmap s in
  let d2 := find_digit (rev_dmap dmap) (rev_s s) in
  d1 * 10 + d2.

Definition sum_ns (xs : list N) : N := fold_left N.add xs 0.
Definition part (ds : list (string * N)) (xs : list string) : N :=
  sum_ns (map (cval ds) xs).

Definition part1 (xs : list string) : N := part digit_map xs.
Definition part2 (xs : list string) : N := part digit_map2 xs.
Definition main (xs : list string) : (N * N) := (part1 xs, part2 xs).

Definition example1 : list string := input
"1abc2"
"pqr3stu8vwx"
"a1b2c3d4e5f"
"treb7uchet"
.

Definition example2 : list string := input
"two1nine"
"eightwothree"
"abcone2threexyz"
"xtwone3four"
"4nineeightseven2"
"zoneight234"
"7pqrstsixteen"
.

Example test_example1: part1 example1 = 142.
Proof. simpl. reflexivity. Qed.

Example test_example2: part2 example2 = 281.
Proof. simpl. reflexivity. Qed.
