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

Definition dig_map : Type := list posn.

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

Definition dig (insns : list insn) : dig_map :=
  let '(x, m) :=
    fold_left
      (fun '(p, m) insn =>
         let p' := offset_by p (direction insn) (distance insn) in
         (p', p :: m))
      insns
      ((0, 0), []) in
  x :: m.

Fixpoint area_ (acc : int) (m : dig_map) : int :=
  match m with
  | p1 :: ((p2 :: _) as m') =>
      let '((x1, y1), (x2, y2)) := (p1, p2) in
      let det := y1 * x2 - x1 * y2 in
      let edge := abs (x2 - x1) + abs (y2 - y1) in
      area_ (acc + det + edge) m'
  | _ => acc
  end.
Definition area (m : dig_map) : int :=
  (area_ 0 m) / 2 + 1.

Definition part1 (m : list insn) := area (dig m).
Definition part2 (m : list insn) := area (dig (map flip_insn m)).

Definition main (m : list insn) := (part1 m, part2 m).

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

Example sample: main example = (62, 952408144115).
Proof. reflexivity. Qed.
