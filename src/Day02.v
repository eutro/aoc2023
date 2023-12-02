From Coq Require Export List NArith.
From Coq Require Import Lia.

Import ListNotations.

#[global] Open Scope N_scope.
#[global] Open Scope bool_scope.

Declare Custom Entry game.
Declare Custom Entry draw.
Declare Custom Entry hand.

Inductive color : Set :=
| red : color
| green : color
| blue : color.

Inductive draw : Set := Draw : (color -> N) -> draw.
Inductive game : Set := GameOf : N -> list draw -> game.

Definition draw_get col draw :=
  let 'Draw f := draw in f col.

Definition col_eq a b :=
  match (a, b) with
  | (red, red) | (green, green) | (blue, blue) => true
  | _ => false
  end.

Definition draw_leb l r :=
  let '(Draw lf, Draw rf) := (l, r) in
  (lf red <=? rf red) &&
    (lf green <=? rf green) &&
    (lf blue <=? rf blue).

Definition game_id gm := let 'GameOf id _ := gm in id.

Fixpoint build_draw_ (col : color) (acc : N) (picks : list (color * N)) : N :=
  match picks with
  | [] => acc
  | (ncol, nn) :: tl =>
      build_draw_ col (acc + if col_eq col ncol then nn else 0) tl
  end.
Definition build_draw (picks : list (color * N)) (col : color) : N :=
  build_draw_ col 0 picks.

Notation "'input' game .. games" :=
  (cons game .. (cons games nil) ..)
    (at level 200, game custom game at level 3, only parsing).
Notation "'Game' id ':' draw ';' .. ';' draws" :=
  (GameOf id (cons draw .. (cons draws nil) ..))
    (in custom game at level 3, id constr at level 2, draw custom draw at level 2).
Notation "hand ',' .. ',' hands" :=
  (Draw (build_draw (cons hand .. (cons hands nil) ..)))
    (in custom draw at level 2, hands custom hand at level 1).
Notation "n color" :=
  (color, n)
    (in custom hand at level 1, color constr at level 0, n constr at level 0).

Definition draw_possible_with (bag : draw) (hand : draw) : bool := draw_leb hand bag.
Definition game_possible_with (bag : draw) (gm : game) : bool :=
  let 'GameOf _ hands := gm in
  forallb (draw_possible_with bag) hands.

Definition game_min_possible_ (gm : game) (col : color) :=
  let 'GameOf _ hands := gm in
  fold_left N.max (map (draw_get col) hands) 0.
Definition game_min_possible (gm : game) : draw := Draw (game_min_possible_ gm).

Definition draw_power (d : draw) : N :=
  let 'Draw df := d in df red * df green * df blue.

Definition part1_bag (col : color) : N :=
  match col with
  | red => 12
  | green => 13
  | blue => 14
  end.

Definition collect_ids (inp : list game) : list N :=
  let possible := filter (game_possible_with (Draw part1_bag)) inp in
  map game_id possible.

Definition collect_powers (inp : list game) : list N :=
  map (fun g => draw_power (game_min_possible g)) inp.

Definition sum_ns ns := fold_left N.add ns 0.

Definition main (inp : list game) : N * N :=
  (sum_ns (collect_ids inp), sum_ns (collect_powers inp)).

Definition example1 := input
Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green
Game 2: 1 blue, 2 green; 3 green, 4 blue, 1 red; 1 green, 1 blue
Game 3: 8 green, 6 blue, 20 red; 5 blue, 4 red, 13 green; 5 green, 1 red
Game 4: 1 green, 3 red, 6 blue; 3 green, 6 red; 3 green, 15 blue, 14 red
Game 5: 6 red, 1 blue, 3 green; 2 blue, 1 red, 2 green
.

Example sample_part1: collect_ids example1 = [1; 2; 5].
Proof. simpl. reflexivity. Qed.

Example sample_part2: collect_powers example1 = [48; 12; 1560; 630; 36].
Proof. simpl. reflexivity. Qed.
