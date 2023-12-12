From Coq Require Export String List NArith ZArith Ascii.
From Coq Require Import Lia Sorting Orders OrdersEx OrdersAlt FMapAVL Program.Wf.

Import IfNotations.
Export StringSyntax ListNotations.

#[global] Open Scope char_scope.
#[global] Open Scope nat_scope.
#[global] Open Scope Z_scope.

Module PosnOrder := PairOrderedType Z_as_OT Z_as_OT.
Module Backport_PosnOrder := Backport_OT PosnOrder.
Module PosnMap := FMapAVL.Make Backport_PosnOrder.
Definition posn : Type := PosnMap.E.t.

Inductive tile : Set :=
| t_ns | t_we | t_ne | t_nw | t_sw | t_se
| t_ground | t_start.
Definition N_of_tile (a : tile) : N :=
  match a with
  | t_ns => 0 | t_we => 1 | t_ne => 2 | t_nw => 3 | t_sw => 4 | t_se => 5
  | t_ground => 6 | t_start => 7
  end.
Definition tile_compare (a b : tile) : comparison :=
  N.compare (N_of_tile a) (N_of_tile b).
Definition tile_ltb (a b : tile) : bool :=
  if tile_compare a b is Lt then true else false.

Definition char_to_tile (c : ascii) : tile :=
  match c with
  | "|" => t_ns | "-" => t_we | "L" => t_ne | "J" => t_nw | "7" => t_sw | "F" => t_se
  | "S" => t_start | _ => t_ground
  end.

Definition inp_grid : Type := PosnMap.t tile.

Fixpoint build_row (m : inp_grid) (row col : Z) (chars : list ascii) : inp_grid :=
  match chars with
  | [] => m
  | c :: chars' =>
      let tile := char_to_tile c in
      let m' := if tile is t_ground then m
                else PosnMap.add (row, col) tile m in
      build_row m' row (Z.succ col) chars'
  end.
Fixpoint build_map_ (m : inp_grid) (row : Z) (ls : list string) : inp_grid :=
  match ls with
  | [] => m
  | row_s :: ls' =>
      let m' := build_row m row 0 (list_ascii_of_string row_s) in
      build_map_ m' (Z.succ row) ls'
  end.
Definition build_map (ls : list string) : inp_grid :=
  build_map_ (PosnMap.empty tile) 0 ls.

Definition find_start (inp : inp_grid) : option posn :=
  PosnMap.fold
    (fun key elt a =>
       match (elt, a) with
       | (t_start, _) => Some key
       | _ => a
       end)
    inp
    None.

Inductive dir : Set := north | south | east | west.
Definition dir_offset (p : posn) (d : dir) : posn :=
  let '(x, y) := p in
  match d with
  | north => (x - 1, y) | south => (x + 1, y)
  | east => (x, y + 1) | west => (x, y - 1)
  end.
Definition dir_opp (d : dir) : dir :=
  match d with
  | north => south | south => north
  | east => west | west => east
  end.
Lemma dir_opp_id: forall d, dir_opp (dir_opp d) = d.
Proof.
  intros d. unfold dir_opp. destruct d.
  reflexivity. reflexivity. reflexivity. reflexivity.
Qed.
Definition pipe_dirs (t : tile) : list dir :=
  match t with
  | t_ns => [north; south] | t_we => [east; west]
  | t_ne => [north; east] | t_nw => [north; west]
  | t_sw => [south; west] | t_se => [east; south]
  | t_ground => []
  | t_start => [north; east; south; west]
  end.
Definition dirs_pipe (d : list dir) : tile :=
  match d with
  | [north; south] => t_ns | [east; west] => t_we
  | [north; east] => t_ne | [north; west] => t_nw
  | [south; west] => t_sw | [east; south] => t_se
  | [north; east; south; west] => t_start
  | _ => t_ground
  end.

Definition posn_eqb (a b : posn) : bool :=
  if PosnOrder.compare a b is Eq then true else false.

Definition find_neighbours {A : Type} (proj : dir * posn -> A)
  (inp : inp_grid) (from : tile * posn) : list (tile * A) :=
  let '(tl, pos) := from in
  let find_it (d : dir) :=
    let pos' := dir_offset pos d in
    match PosnMap.find pos' inp with
    | None => []
    | Some tl' =>
        let tl'_nbs := List.map (dir_offset pos') (pipe_dirs tl') in
        if List.existsb (posn_eqb pos) tl'_nbs
        then [(tl', proj (d, pos'))]
        else []
    end in
  List.flat_map find_it (pipe_dirs tl).
Fixpoint find_loop_ (sz : nat) (inp : inp_grid) (start : (tile * posn)) : list (tile * posn) :=
  match sz with
  | O => []
  | S sz' =>
      match find_neighbours snd inp start with
      | [] => []
      | nb :: _ => nb :: find_loop_ sz' (PosnMap.remove (snd nb) inp) nb
      end
  end.
Definition find_loop (inp : inp_grid) (start : posn) : list (tile * posn) :=
  find_loop_ (PosnMap.cardinal inp) inp (t_start, start).

Definition replace_start (inp : inp_grid) (start : posn) : inp_grid :=
  let dirs := List.map snd (find_neighbours fst inp (t_start, start)) in
  let new_tile := dirs_pipe dirs in
  PosnMap.add start new_tile inp.

Definition quad (t : Type) : Type := t * t * t * t.
Definition mkq {A : Type} (a b c d : A) : quad A := (a, b, c, d).
Definition quad_side {A : Type} (d : dir) (q : quad A) : A * A :=
  let '(nw, ne, sw, se) := q in
  match d with
  | north => (nw, ne)
  | south => (sw, se)
  | east => (ne, se)
  | west => (nw, sw)
  end.
Definition fill_repr (til : tile) (i : bool) : quad bool :=
  let o := negb i in
  match til with
  | t_ns => mkq o i
               o i
  | t_we => mkq o o
               i i
  | t_ne => mkq o i
               o o
  | t_nw => mkq i o
               o o
  | t_sw => mkq o o
               i o
  | t_se => mkq o o
               o i
  | t_ground => mkq i i
                   i i
  | t_start => mkq i i
                  i i
  end.

Definition transition (src dst : tile) (d : dir) : bool -> bool :=
  let src_repr := fill_repr src true in
  let dst_irepr := fill_repr dst true in
  let '(s0, s1) := quad_side d src_repr in
  let '(d0, d1) := quad_side (dir_opp d) dst_irepr in
  let no_flip := (Bool.eqb s0 d0) || (Bool.eqb s1 d1) in
  if no_flip then id else negb.

Example transition_ns_east_ns: transition t_ns t_ns east = negb.
Proof. reflexivity. Qed.
Example transition_ns_south_ns: transition t_ns t_ns south = id.
Proof. reflexivity. Qed.
Example transition_ground_any_ground: forall (d : dir), transition t_ground t_ground d = id.
Proof. intros d. destruct d. reflexivity. reflexivity. reflexivity. reflexivity. Qed.
Example transition_ground_south_we: transition t_ground t_we south = negb.
Proof. reflexivity. Qed.

Fixpoint find_minmax_ (mn mx : posn) (ps : list posn) : posn * posn :=
  let '((mn_x, mn_y), (mx_x, mx_y)) := (mn, mx) in
  match ps with
  | (x, y) :: ps' => find_minmax_ (Z.min x mn_x, Z.min y mn_y) (Z.max x mx_x, Z.max y mx_y) ps'
  | [] => (mn, mx)
  end.
Definition find_minmax (ps : list posn) : posn * posn :=
  match ps with
  | p :: ps' => find_minmax_ p p ps'
  | [] => ((0, 0), (0, 0))
  end.

Definition build_from_loop (loop : list (tile * posn)) : inp_grid :=
  List.fold_left
    (fun m '(tl, pos) => PosnMap.add pos tl m)
    loop (PosnMap.empty tile).

Section Counting.
  Variables (A : Type).
  Variable inp : inp_grid.
  Variable acc_succ : posn -> A -> A.
  Variable acc_init : A.

  Fixpoint count_row (acc : A) (rem : nat) (row col : Z) (src : tile) (inside : bool) : A :=
    let pos := (row, col) in
    let dst := match PosnMap.find pos inp with Some x => x | None => t_ground end in
    let inside' := transition src dst east inside in
    let is_ground := if dst is t_ground then true else false in
    let maybe_succ := if is_ground && inside' then acc_succ pos else id in
    let acc' := maybe_succ acc in
    match rem with
    | O => acc'
    | S rem' => count_row acc' rem' row (Z.succ col) dst inside'
    end.
  Fixpoint count_rows (acc : A) (rem : nat) (row : Z) (y_range : Z * Z) : A :=
    let '(mn_y, mx_y) := y_range in
    let acc' := count_row acc (Z.to_nat (mx_y - mn_y)) row mn_y t_ground false in
    match rem with
    | O => acc'
    | S rem' => count_rows acc' rem' (Z.succ row) y_range
    end.
  Definition count_inside_ (mn mx : posn) : A :=
    let '((mn_x, mn_y), (mx_x, mx_y)) := (mn, mx) in
    count_rows acc_init (Z.to_nat (mx_x - mn_x)) mn_x (mn_y, mx_y).
End Counting.
Definition count_inside (inp : inp_grid) (mn mx : posn) : N :=
  count_inside_ N inp (fun _ => N.succ) 0%N mn mx.
Definition enum_inside (inp : inp_grid) (mn mx : posn) : list posn :=
  count_inside_ (list posn) inp cons [] mn mx.

Definition main (inp : inp_grid) :=
  let start_pos := match find_start inp with | None => (0, 0) | Some x => x end in
  let loop := find_loop (replace_start inp start_pos) start_pos in
  let len := N.of_nat (List.length loop) in
  let part1 := (len / 2)%N in
  let grid' := build_from_loop loop in
  let '(mn, mx) := find_minmax (List.map snd loop) in
  let part2 := count_inside grid' mn mx in
  (part1, part2).

#[global] Open Scope string_scope.

Notation "'input' line .. lines" :=
  (build_map (cons line .. (cons lines nil) ..))
    (at level 200, line at level 0, only parsing).

Definition example1 := input
"....."
".S-7."
".|.|."
".L-J."
"....."
.

Definition example2 := input
"..F7."
".FJ|."
"SJ.L7"
"|F--J"
"LJ..."
.

Definition example3 := input
".F----7F7F7F7F-7...."
".|F--7||||||||FJ...."
".||.FJ||||||||L7...."
"FJL7L7LJLJ||LJ.L-7.."
"L--J.L7...LJS7F-7L7."
"....F-J..F7FJ|L7L7L7"
"....L7.F7||L7|.L7L7|"
".....|FJLJ|FJ|F7|.LJ"
"....FJL-7.||.||||..."
"....L---J.LJ.LJLJ..."
.

Definition example4 := input
"FF7FSF7F7F7F7F7F---7"
"L|LJ||||||||||||F--J"
"FL-7LJLJ||||||LJL-77"
"F--JF--7||LJLJ7F7FJ-"
"L---JF-JLJ.||-FJLJJ7"
"|F|F-JF---7F7-L7L|7|"
"|FFJF7L7F-JF7|JL---7"
"7-L-JL7||F7|L7F-7F7|"
"L.L7LFJ|||||FJL7||LJ"
"L7JLJL-JLJLJL--JLJ.L"
.

Example sample1: fst (main example1) = 4%N.
Proof. reflexivity. Qed.
Example sample2: fst (main example2) = 8%N.
Proof. reflexivity. Qed.
Example sample3: snd (main example3) = 8%N.
Proof. reflexivity. Qed.
Example sample4: snd (main example4) = 10%N.
Proof. reflexivity. Qed.
