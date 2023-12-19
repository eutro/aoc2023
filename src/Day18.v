From Coq Require Export String List NArith ZArith Ascii Sint63.
From Coq Require Import Lia Sorting Orders OrdersEx OrdersAlt FMapAVL PArray Program.Wf.
From Aoc2023 Require Import OrderUtils.

Import IfNotations.
Export StringSyntax ListNotations.

#[global] Open Scope char_scope.
#[global] Open Scope sint63_scope.
#[global] Open Scope array_scope.

Module Int63_OT.
  Module T.
    Definition t := int.
    Definition map := to_Z.
  End T.
  Module Z_as_OTA := OT_to_Alt Z_as_OT.
  Module Int63_OTA := OrderByFun T Z_as_OTA T.
  Module Int63_as_OT := OT_from_Alt Int63_OTA.
  Include Int63_as_OT.
End Int63_OT.
Module PosnOrder := PairOrderedType Int63_OT Int63_OT.
Module Backport_PosnOrder := Backport_OT PosnOrder.
Module PosnMap := FMapAVL.Make Backport_PosnOrder.
Definition posn : Type := PosnMap.E.t.

Definition dig_map : Type := PosnMap.t int.
Definition dig_state : Type := posn * dig_map.

Inductive dir : Set := right | left | down | up.

Inductive insn : Set :=
  mkInsn
    { direction : dir
    ; distance : int
    ; colour : int }.

Definition dir_map :=
  let m0 := PArray.make 4 up in
  let m1 := m0.[0 <- right] in
  let m2 := m1.[1 <- down] in
  let m3 := m2.[2 <- left] in
  m3.
Definition flip_insn (i : insn) : insn :=
  let c := colour i in
  let dir' := dir_map.[c mod 16] in
  let dist' := c / 16 in
  mkInsn dir' dist' (-1).

Definition offset_by (p : posn) (d : dir) (sf : int) : posn :=
  let '(x, y) := p in
  match d with
  | right => (x + sf, y)
  | left => (x - sf, y)
  | up => (x, y - sf)
  | down => (x, y + sf)
  end.
Definition offset p d := offset_by p d 1.

Fixpoint dig2 (m : dig_map) (p : posn) (i : insn) (rem : nat) : dig_state :=
  match rem with
  | O => (p, m)
  | S rem' =>
      let p' := offset p (direction i) in
      let m' := PosnMap.add p' (colour i) m in
      dig2 m' p' i rem'
  end.
Definition dig1 (m : dig_state) (i : insn) : dig_state :=
  let '(pos, map) := m in
  dig2 map pos i (Z.to_nat (to_Z (distance i))).
Fixpoint dig (m : dig_state) (insns : list insn) : dig_state :=
  match insns with
  | [] => m
  | insn :: insns' => dig (dig1 m insn) insns'
  end.

Definition start_dig (insns : list insn) : dig_map :=
  let m := ((0, 0), PosnMap.empty int) in
  snd (dig m insns).

Definition min (a b : int) : int := if a <? b then a else b.
Definition max (a b : int) : int := if a <? b then b else a.

Definition get_size (pmin pmax : posn) : int :=
  let '((minx, miny), (maxx, maxy)) := (pmin, pmax) in
  (maxx + 1 - minx) * (maxy + 1 - miny).

Definition in_bounds (pmin pmax p : posn) : bool :=
  let '((minx, miny), (maxx, maxy)) := (pmin, pmax) in
  let '(x, y) := p in
  (minx <=? x) && (x <=? maxx) &&
    (miny <=? y) && (y <=? maxy).
Fixpoint flood_ (pmin pmax : posn) (m : dig_map) (q : list posn) (fuel : nat) : dig_map :=
  match (fuel, q) with
  | (O, _) | (_, []) => m
  | (S fuel', p :: q') =>
      let is_ok p := in_bounds pmin pmax p && negb (PosnMap.mem p m) in
      let neighbours := filter is_ok (map (offset p) [left; right; up; down]) in
      let q' := neighbours ++ q' in
      let m' := fold_left (fun m p => PosnMap.add p (-1) m) neighbours m in
      flood_ pmin pmax m' q' fuel'
  end.
Definition flood (m : dig_map) (start : posn) (pmin pmax : posn) : dig_map :=
  let sz_n := Z.to_nat (to_Z (get_size pmin pmax)) in
  flood_ pmin pmax (PosnMap.add start (-1) m) [start] sz_n.

Definition fill_count (m : dig_map) :=
  let extreme f :=
    PosnMap.fold
      (fun k v best =>
         (f (fst best) (fst k),
           f (snd best) (snd k)))
      m (0, 0) in
  let '(pmin, pmax) := (extreme min, extreme max) in
  let pmin' := offset (offset pmin left) up in
  let pmax' := offset (offset pmax right) down in
  let flooded := flood m pmin' pmin' pmax' in
  get_size pmin' pmax' -
    of_Z (Z.of_nat (PosnMap.cardinal flooded)) +
    of_Z (Z.of_nat (PosnMap.cardinal m)).

Definition part1 (m : list insn) :=
  let dug := start_dig m in
  fill_count dug.

Definition main (m : list insn) := part1 m.

Definition int_of_ascii (a : ascii) : int :=
  of_Z (Z.of_N (N_of_ascii a)).
Definition parse_hex (n : string) : int :=
  let hex_digit d :=
    int_of_ascii d -
    (if ("0" <=? d) && (d <=? "9") then int_of_ascii "0"
     else if ("a" <=? d) && (d <=? "f") then int_of_ascii "a" - 10
          else if ("A" <=? d) && (d <=? "F") then int_of_ascii "A" - 10
               else int_of_ascii d)%char in
  let digits := map hex_digit (list_ascii_of_string n) in
  let horner acc d := (16 * acc) + d in
  List.fold_left horner digits 0.

Declare Custom Entry dir.
Declare Custom Entry insn.
Notation "'input' insn .. insns" :=
  (cons insn .. (cons insns nil) ..)
    (at level 200, insn custom insn at level 3, only parsing).

Notation "dir dist '(#' hex_num ')'" :=
  (mkInsn dir dist (parse_hex hex_num%string))
    (in custom insn at level 3,
        dir custom dir at level 0,
        dist constr at level 0,
        hex_num constr at level 0).

Notation "'R'" := right (in custom dir at level 0).
Notation "'L'" := left (in custom dir at level 0).
Notation "'U'" := up (in custom dir at level 0).
Notation "'D'" := down (in custom dir at level 0).

Definition example := input
R 6 (#"70c710")
D 5 (#"0dc571")
L 2 (#"5713f0")
D 2 (#"d2c081")
R 2 (#"59c680")
D 2 (#"411b91")
L 5 (#"8ceee2")
U 2 (#"caa173")
L 1 (#"1b58a2")
U 2 (#"caa171")
R 2 (#"7807d2")
U 3 (#"a77fa3")
L 2 (#"015232")
U 2 (#"7a21e3")
.

Compute main example.
