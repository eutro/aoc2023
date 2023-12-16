From Coq Require Export String List NArith ZArith Ascii Uint63.
From Coq Require Import Lia Sorting Orders OrdersEx OrdersAlt FMapAVL PArray Program.Wf.
From Aoc2023 Require Import OrderUtils.

Import IfNotations.
Export StringSyntax ListNotations.

#[global] Open Scope char_scope.
#[global] Open Scope Z_scope.
#[global] Open Scope array_scope.

Module PosnOrder := PairOrderedType Z_as_OT Z_as_OT.
Module Backport_PosnOrder := Backport_OT PosnOrder.
Module PosnMap := FMapAVL.Make Backport_PosnOrder.
Definition posn : Type := PosnMap.E.t.
Definition posn_set : Type := PosnMap.t unit.

Inductive mirror : Set :=
  | split_h | split_v | diag_ur | diag_ul.
Definition mirror_of_char (c : ascii) : option mirror :=
  match c with
  | "-" => Some split_h
  | "|" => Some split_v
  | "/" => Some diag_ur
  | "\" => Some diag_ul
  | _ => None
  end.
Definition char_of_mirror (m : option mirror) :=
  match m with
  | Some split_h => "-"
  | Some split_v => "|"
  | Some diag_ur => "/"
  | Some diag_ul => "\"
  | None => "."
  end.
Inductive dir : Set := up | down | left | right.
Definition dir_offset (d : dir) (p : posn) : posn :=
  let '(x, y) := p in
  match d with
  | up => (x - 1, y)
  | down => (x + 1, y)
  | left => (x, y - 1)
  | right => (x, y + 1)
  end.
Definition dir_hit (d : dir) (m : option mirror) : list dir :=
  match m with
  | None => [d]
  | Some m' =>
      match (d, m') with
      | ((left | right), split_h) => [d]
      | ((left | right), split_v) => [up; down]
      | ((up | down), split_v) => [d]
      | ((up | down), split_h) => [left; right]
      | (right, diag_ur) | (left, diag_ul) => [up]
      | (up, diag_ur) | (down, diag_ul) => [right]
      | (left, diag_ur) | (right, diag_ul) => [down]
      | (down, diag_ur) | (up, diag_ul) => [left]
      end
  end.
Definition Z_of_dir (d : dir) : Z :=
  match d with up => 0 | down => 1 | right => 2 | left => 3 end.

Module Dir.
  Definition t : Type := dir.
  Definition map := Z_of_dir.
End Dir.

Module Z_Alt := OT_to_Alt Z_as_OT.
Module DirOrder := OrderByFun Dir Z_Alt Dir.
Module DirOrder_OT := OT_from_Alt DirOrder.
Module PosnDirOrd := PairOrderedType PosnOrder DirOrder_OT.
Module Backport_PosnDirOrd := Backport_OT PosnDirOrd.
Module PosnDirMap := FMapAVL.Make Backport_PosnDirOrd.
Definition posn_dir_set : Type := PosnDirMap.t unit.

Inductive inp_ty : Type :=
  mkInp
    { mirrors : PosnMap.t mirror
    ; size : Z * Z }.
Definition with_size t sz : inp_ty :=
  {| mirrors := mirrors t ; size := sz |}.
Definition with_mirrors t mr : inp_ty :=
  {| mirrors := mr ; size := size t |}.
Definition inp_max_cover t : nat :=
  let '(w, h) := size t in
  Z.to_nat (4 * w * h)%Z.

Fixpoint build_row (m : inp_ty) (row col : Z) (chars : list ascii) : inp_ty :=
  match chars with
  | [] => with_size m (Z.succ row, col)
  | c :: chars' =>
      let m' :=
        match mirror_of_char c with
        | Some mir => with_mirrors m (PosnMap.add (row, col) mir (mirrors m))
        | None => m
        end in
      build_row m' row (Z.succ col) chars'
  end.
Fixpoint build_map_ (m : inp_ty) (row : Z) (ls : list string) : inp_ty :=
  match ls with
  | [] => m
  | row_s :: ls' =>
      let m' := build_row m row 0 (list_ascii_of_string row_s) in
      build_map_ m' (Z.succ row) ls'
  end.
Definition build_map (lns : list string) : inp_ty :=
  build_map_ (mkInp (PosnMap.empty mirror) (0, 0)) 0 lns.

Section Step.
  Variable m : inp_ty.

  Definition in_bounds (p : posn) : bool :=
    let '(x, y) := p in
    let '(w, h) := size m in
    (0 <=? x) && (x <? w) && (0 <=? y) && (y <? h).

  Definition add_posns seen ls := List.fold_left (fun seen st => PosnDirMap.add st tt seen) ls seen.

  Fixpoint try_step (s : list (posn * dir)) (seen : posn_dir_set) : option (list (posn * dir) * posn_dir_set) :=
    match s with
    | [] => None
    | (p, d) :: s' =>
        let p' := dir_offset d p in
        if negb (in_bounds p') then try_step s' seen else
          let d's := dir_hit d (PosnMap.find p' (mirrors m)) in
          let new_s := List.map (fun d' => (p', d')) d's in
          let unseen_new_s :=
            List.filter
              (fun st => negb (PosnDirMap.mem st seen))
              new_s in
          let seen' := add_posns seen unseen_new_s in
          match unseen_new_s with
          | [] => try_step s' seen
          | _ => Some (unseen_new_s ++ s', seen')
          end
    end.
  Fixpoint step_dirs_ (fuel : nat) (s : list (posn * dir)) (seen : posn_dir_set) : posn_dir_set :=
    match fuel with
    | O => seen
    | S fuel' =>
        match try_step s seen with
        | None => seen
        | Some (s', seen') => step_dirs_ fuel' s' seen'
        end
    end.
  Definition step_dirs (s : list (posn * dir)) : posn_dir_set :=
    step_dirs_ (inp_max_cover m) s (PosnDirMap.empty unit).
End Step.
Definition project_posn_dir_set (s : posn_dir_set) : posn_set :=
  PosnDirMap.fold (fun k tt out => PosnMap.add (fst k) tt out) s (PosnMap.empty unit).

Section PrintMap.
  Variables (f : posn -> ascii) (sz : Z * Z).
  Definition print_map_char (row col : N) (s : list ascii) : list ascii :=
    let c := f (Z.of_N row, Z.of_N col) in
    c :: s.
Definition print_map_row (row : N) (rs : list string) : list string :=
  string_of_list_ascii (List.rev (N.recursion [] (print_map_char row) (Z.to_N (snd sz)))) :: rs.
Definition print_map : list string :=
  List.rev (N.recursion [] print_map_row (Z.to_N (fst sz))).
End PrintMap.
Definition print_inp (m : inp_ty) : list string :=
  print_map (fun p => char_of_mirror (PosnMap.find p (mirrors m))) (size m).

Definition step_part1 (m : inp_ty) : posn_dir_set :=
  step_dirs m [((0, -1), right)].

Definition print_part1 (m : inp_ty) : list string :=
  let pds := step_part1 m in
  let f (p : posn) :=
    let dirs := List.filter (fun d => PosnDirMap.mem (p, d) pds) [up; down; left; right] in
    let mirror := PosnMap.find p (mirrors m) in
    match mirror with
    | None =>
        match dirs with
        | [] => "."
        | [left] => "<" | [right] => ">" | [up] => "^" | [down] => "v"
        | [_; _] => "2" | [_; _; _] => "3" | _ => "4" end
    | _ => char_of_mirror mirror
    end in
  print_map f (size m).

Definition count_posn_dir_set pds : Z := Z.of_nat (PosnMap.cardinal (project_posn_dir_set pds)).
Definition part1 (m : inp_ty) : Z := count_posn_dir_set (step_part1 m).

Definition part2 (m : inp_ty) : Z :=
  let '(w, h) := size m in
  let xs := N.recursion [] cons (Z.to_N w)in
  let ys := N.recursion [] cons (Z.to_N h) in
  let starts :=
    List.map (fun x => ((Z.of_N x, -1), right)) xs ++
    List.map (fun x => ((Z.of_N x, h), left)) xs ++
    List.map (fun y => ((-1, Z.of_N y), down)) ys ++
    List.map (fun y => ((w, Z.of_N y), up)) ys in
  List.fold_left
    (fun best start =>
       let attempt := step_dirs m [start] in
       Z.max best (count_posn_dir_set attempt))
    starts 0.

Definition main (m : inp_ty) :=
  (part1 m, part2 m).

Notation "'input' line .. lines" :=
  (build_map (cons line%string .. (cons lines%string nil) ..))
    (at level 200, line at level 0, only parsing).
Notation "'grid' line .. lines" :=
  (cons line%string .. (cons lines%string nil) ..)
    (at level 200, line at level 0,
      format "'grid' '//' line '//' .. '//' lines").

Definition example := input
".|...\...."
"|.-.\....."
".....|-..."
"........|."
".........."
".........\"
"..../.\\.."
".-.-/..|.."
".|....-|.\"
"..//.|...."
.

Example sample: main example = (46, 51).
Proof. reflexivity. Qed.
