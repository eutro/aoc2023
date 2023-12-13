From Coq Require Export String List NArith Ascii.
From Coq Require Import Lia Sorting Orders OrdersEx OrdersAlt FMapAVL Program.Wf.

Import IfNotations.
Export StringSyntax ListNotations.

#[global] Open Scope char_scope.
#[global] Open Scope nat_scope.
#[global] Open Scope N_scope.

Inductive mirror : Set :=
| m_horiz : N -> mirror
| m_vert : N -> mirror.

Fixpoint uncons_line {A : Type} (above : list (list A)) : list A * list (list A) :=
  match above with
  | (x :: row) :: tl =>
      let '(xtl, above') := uncons_line tl in
      (x :: xtl, row :: above')
  | [] :: tl => uncons_line tl
  | [] => ([], [])
  end.
Fixpoint transpose_ {A : Type} (len : nat) (xss : list (list A)) : list (list A) :=
  match len with
  | O => []
  | S m =>
      let '(xs, tl) := uncons_line xss in
      xs :: transpose_ m tl
  end.
Definition transpose {A : Type} (xss : list (list A)) : list (list A) :=
  let len := fold_left max (map (length (A:=A)) xss) O in
  transpose_ len xss.

Section Reflection.
  Variable smudges : N.

  Fixpoint check_reflection_ (s : N) (refl grid : list (list ascii)) : bool :=
    match (refl, grid) with
    | ([], _) | (_, []) => s =? 0
    | (l::refl', r::grid') =>
        let del := List.fold_left
                     (fun acc '(l, r) =>
                        if (l =? r)%char
                        then acc
                        else N.succ acc)
                     (List.combine r l) 0 in
        if del <=? s
        then check_reflection_ (s - del) refl' grid'
        else false
    end.
  Definition check_reflection (refl grid : list (list ascii)) : bool :=
    check_reflection_ smudges refl grid.

  Fixpoint find_reflection_ (i : N) (refl grid : list (list ascii)) : option N :=
    match (refl, grid) with
    | ([], _) | (_, []) => None
    | (_, row::grid') =>
        if check_reflection refl grid
        then Some i (*N.of_nat (List.length refl)*)
        else find_reflection_ (N.succ i) (row::refl) grid'
    end.
  Definition find_reflection (grid : list (list ascii)) : option N :=
    match grid with
    | hd :: tl => find_reflection_ 1 [hd] tl
    | [] => None
    end.
  Definition find_either_reflection (grid : list (list ascii)) : option mirror :=
    match find_reflection grid with
    | Some horiz => Some (m_horiz horiz)
    | None => match find_reflection (transpose grid) with
              | Some vert => Some (m_vert vert)
              | None => None
              end
    end.
End Reflection.

Definition refl_to_N (r : option mirror) : N :=
  match r with
  | None => 100000
  | Some (m_horiz h) => 100 * h
  | Some (m_vert v) => v
  end.

Definition part (s : N) (inp : list (list (list ascii))) :=
  let refls := List.map (find_either_reflection s) inp in
  List.fold_left N.add (List.map refl_to_N refls) 0.

Definition main (inp : list (list (list ascii))) :=
  (part 0 inp, part 1 inp).

Declare Custom Entry patt.
Notation "'input' pat ';' .. ';' pats" :=
  (cons pat .. (cons pats nil) ..)
    (at level 200, pat custom patt at level 2, only parsing).
Notation "line .. lines" :=
  (cons (list_ascii_of_string line) .. (cons (list_ascii_of_string lines) nil) ..)
    (in custom patt at level 2, line constr at level 1).

Definition example := input
"#.##..##."
"..#.##.#."
"##......#"
"##......#"
"..#.##.#."
"..##..##."
"#.#.##.#."
;
"#...##..#"
"#....#..#"
"..##..###"
"#####.##."
"#####.##."
"..##..###"
"#....#..#"
.

Compute main example.
