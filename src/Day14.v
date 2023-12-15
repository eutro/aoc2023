From Coq Require Export String List NArith Ascii.
From Coq Require Import Lia Sorting Orders OrdersEx OrdersAlt FMapAVL Program.Wf.

Import IfNotations.
Export StringSyntax ListNotations.

#[global] Open Scope char_scope.
#[global] Open Scope nat_scope.
#[global] Open Scope N_scope.

Module PosnOrder := PairOrderedType N N.
Module Backport_PosnOrder := Backport_OT PosnOrder.
Module PosnMap := FMapAVL.Make Backport_PosnOrder.
Definition posn : Type := PosnMap.E.t.
Definition posn_set : Type := PosnMap.t unit.

Record inp_ty : Type :=
  mkInp
    { rounded_rocks : posn_set
    ; square_rocks : posn_set
    ; size : (N * N) }.
Definition with_rounded_rocks i rr :=
  {| rounded_rocks := rr ; square_rocks := square_rocks i ; size := size i |}.
Definition with_square_rocks i sr :=
  {| rounded_rocks := rounded_rocks i ; square_rocks := sr ; size := size i |}.
Definition with_size i sz :=
  {| rounded_rocks := rounded_rocks i ; square_rocks := square_rocks i ; size := sz |}.

Fixpoint build_row (m : inp_ty) (row col : N) (chars : list ascii) : inp_ty :=
  match chars with
  | [] => with_size m (N.succ row, col)
  | c :: chars' =>
      let m' :=
        match c with
        | "O" => with_rounded_rocks m (PosnMap.add (row, col) tt (rounded_rocks m))
        | "#" => with_square_rocks m (PosnMap.add (row, col) tt (square_rocks m))
        | _ => m
        end in
      build_row m' row (N.succ col) chars'
  end.
Fixpoint build_map_ (m : inp_ty) (row : N) (ls : list string) : inp_ty :=
  match ls with
  | [] => m
  | row_s :: ls' =>
      let m' := build_row m row 0 (list_ascii_of_string row_s) in
      build_map_ m' (N.succ row) ls'
  end.
Definition build_map (lns : list string) : inp_ty :=
  build_map_ (mkInp (PosnMap.empty unit) (PosnMap.empty unit) (0, 0)) 0 lns.

Definition print_map_char (m : inp_ty) (row col : N) (s : list ascii) : list ascii :=
  let has_square := PosnMap.mem (row, col) (square_rocks m) in
  let has_round := PosnMap.mem (row, col) (rounded_rocks m) in
  let c :=
    match (has_square, has_round) with
    | (true, false) => "#"
    | (false, true) => "O"
    | (true, true) => "!"
    | (false, false) => "."
    end in
  c :: s.
Definition print_map_row (m : inp_ty) (row : N) (rs : list string) : list string :=
  string_of_list_ascii (List.rev (N.recursion [] (print_map_char m row) (snd (size m)))) :: rs.
Definition print_map (m : inp_ty) : list string :=
  List.rev (N.recursion [] (print_map_row m) (fst (size m))).

Notation "'input' line .. lines" :=
  (build_map (cons line .. (cons lines nil) ..))
    (at level 200, line at level 0, only parsing).
Notation "'grid' line .. lines" :=
  (cons line%string .. (cons lines%string nil) ..)
    (at level 200, line at level 0,
      format "'grid' '//' line '//' .. '//' lines").

Inductive tilt_dir : Set := north | west | south | east.
Section Tilt.
  Variables (dir : tilt_dir) (m : inp_ty).

  Definition xf (p : posn) : posn :=
    match dir with
    | north => p
    | south => (fst (size m) - fst p - 1, snd p)
    | west => (snd p, fst p)
    | east => (snd p, fst (size m) - fst p - 1)
    end.
  Definition row_sz :=
    match dir with
    | north | south => fst (size m)
    | east | west => snd (size m)
    end.
  Definition col_sz :=
    match dir with
    | north | south => snd (size m)
    | east | west => fst (size m)
    end.

  Fixpoint tilt_col_ (row col : N) (rem : nat) (placement_row : N) (s : posn_set) : posn_set :=
    match rem with
    | O => s
    | S rem' =>
        let here := xf (row, col) in
        let has_sqr := PosnMap.mem here (square_rocks m) in
        let cur_placement_row := if has_sqr then N.succ row else placement_row in
        let should_place := PosnMap.mem here (rounded_rocks m) in
        let (s', placement_row') :=
          if should_place
          then (PosnMap.add (xf (cur_placement_row, col)) tt s, N.succ cur_placement_row)
          else (s, cur_placement_row) in
        tilt_col_ (N.succ row) col rem' placement_row' s'
    end.
  Definition tilt_col (col : N) (s : posn_set) : posn_set :=
    tilt_col_ 0 col (N.to_nat row_sz) 0 s.
  Definition tilt : inp_ty :=
    let rr := N.recursion (PosnMap.empty unit) tilt_col col_sz in
    with_rounded_rocks m rr.
End Tilt.
Definition tilt_cycle m := tilt east (tilt south (tilt west (tilt north m))).

Definition tilt_cycles_fast (ntimes : N) (m : inp_ty) : inp_ty :=
  N.recursion m (fun _ m => tilt_cycle m) ntimes.
Definition rocks_eqb (m1 m2 : inp_ty) : bool :=
  PosnMap.equal (fun _ _ => true) (rounded_rocks m1) (rounded_rocks m2).
Fixpoint tilt_cycles_ (fuel : nat) (ntimes : N) (diff : N) (slow fast : inp_ty) : option (N * N) * inp_ty :=
  match fuel with
  | O => (None, fast)
  | S O => (None, tilt_cycle fast)
  | S (S fuel') =>
      let ntimes' := ntimes - 2 in
      let slow' := tilt_cycle slow in
      let fast' := tilt_cycle (tilt_cycle fast) in
      let diff' := N.succ diff in
      if rocks_eqb slow' fast'
      then
        (* tilt_cycle^diff slow = fast,
         -> forall n, tilt_cycle^(n*diff) fast = fast,
         thus,
         tilt_cycle^ntimes fast = tilt_cycle^(ntimes mod diff) fast*)
        (Some (diff', ntimes'),
          tilt_cycles_fast (ntimes' mod diff') fast')
      else tilt_cycles_ fuel' ntimes' diff' slow' fast'
  end.

Definition tilt_cycles0 (ntimes : N) (m : inp_ty) : option (N * N) * inp_ty :=
  tilt_cycles_ (N.to_nat (N.min ntimes 10000)) ntimes 0 m m.
Definition tilt_cycles (ntimes : N) (m : inp_ty) : inp_ty :=
  snd (tilt_cycles0 ntimes m).

Fixpoint iterate {A : Type} (ntimes : nat) (f : A -> A) (i : A) : list A :=
  match ntimes with
  | O => [i]
  | S n' => i :: iterate n' f (f i)
  end.

Definition posn_load (nrows : N) (p : posn) := nrows - fst p.
Definition compute_load (m : inp_ty) : N :=
  let rocks := List.map fst (PosnMap.elements (rounded_rocks m)) in
  let loads := List.map (posn_load (fst (size m))) rocks in
  fold_left N.add loads 0.

Definition main (m : inp_ty) :=
  (compute_load (tilt north m),
    compute_load (tilt_cycles 1000000000 m)).

#[global] Open Scope string_scope.

Definition example := input
"O....#...."
"O.OO#....#"
".....##..."
"OO.#O....O"
".O.....O#."
"O.#..O.#.#"
"..O..#O..O"
".......O.."
"#....###.."
"#OO..#...."
.

Example sample: main example = (136, 64).
Proof. reflexivity. Qed.
