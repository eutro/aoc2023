From Coq Require Export String List NArith.
From Coq Require Import Lia Ascii Sorting Orders OrdersEx.

Import ListNotations.
Import StringSyntax.
Import AsciiSyntax.

#[global] Open Scope string_scope.
#[global] Open Scope N_scope.

Inductive sym : Set :=
| empty : sym
| op : (* pos *) (N * N) -> ascii -> sym
| num : (* pos *) (N * N) -> (* value *) N -> sym
| digit : N -> sym.
Definition id_eqb (a b : N * N) :=
  let '((l1, r1), (l2, r2)) := (a, b) in
  (l1 =? l2) && (r1 =? r2).
Definition sym_eqb (a b : sym) :=
  match (a, b) with
  | (empty, empty) => true
  | (op id1 a, op id2 b) => id_eqb id1 id2 && Ascii.eqb a b
  | (num id1 v1, num id2 v2) => id_eqb id1 id2 && (v1 =? v2)
  | (digit v1, digit v2) => v1 =? v2
  | _ => false
  end.

Open Scope char_scope.
Definition sym_of_ascii (c : ascii) : sym :=
  match c with
  | "." => empty
  | "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8"
  | "9" => digit ((N_of_ascii c) - (N_of_ascii "0"))
  | _ => op (0, 0) c
  end.
Close Scope char_scope.

Fixpoint cons_repeat {A : Type} (n : nat) (x : A) (l : list A) :=
  match n with
  | O => l
  | S m => x :: cons_repeat m x l
  end.

Fixpoint relex_line (lno : N) (cno : N) (ln : list sym) :=
  match ln with
  | [] => []
  | digit d :: tl =>
      (fix parse_int acc cno' l :=
         match l with
         | digit d :: tl => parse_int (10 * acc + d) (cno' + 1) tl
         | _ => cons_repeat (N.to_nat (cno' - cno)) (num (lno, cno) acc) (relex_line lno cno' l)
         end) d (cno + 1) tl
  | op _ c :: tl => op (lno, cno) c :: relex_line lno (cno + 1) tl
  | c :: tl => c :: relex_line lno (cno + 1) tl
  end.
Fixpoint relex_ (lno : N) (lines : list (list sym)) :=
  match lines with
  | [] => []
  | ln :: tl => relex_line lno 0 ln :: relex_ (lno + 1) tl
  end.
Definition relex (syms : list (list sym)) := relex_ 0 syms.
Definition parse_lines (lns : list string) : list (list sym) :=
  relex (map (fun s => map sym_of_ascii (list_ascii_of_string s)) lns).
Notation "'input' line .. lines" :=
  (parse_lines (cons line .. (cons lines nil) ..))
    (at level 200, line at level 0, only parsing).

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

Fixpoint diag_ {A : Type} (above : list (list A)) (xss : list (list A)) : list (list A) :=
  match xss with
  | (x :: row) :: tl =>
      let '(xtl, above') := uncons_line above in
      (x :: xtl) :: diag_ (row :: above') tl
  | _ => transpose above
  end.
Definition diag {A : Type} (xss : list (list A)) : list (list A) := diag_ [] xss.
Definition odiag {A : Type} (xss : list (list A)) : list (list A) := diag (rev xss).
Definition angles (xs : list (list sym)) :=
  flat_map (fun f => f xs) [id; transpose; diag; odiag].

Definition Part : Set := (N * N) * N.
Module Part_LHS_OT := PairOrderedType N_as_OT N_as_OT.
Module Part_OT := PairOrderedType Part_LHS_OT N_as_OT.
Module Part_OTF := OT_to_Full Part_OT.
Module Part_TTLB := OTF_to_TTLB Part_OTF.
Module SortPart := Sort Part_TTLB.
Definition part_eqb (lhs rhs : Part) :=
  let '(((l1, c1), v1), ((l2, c2), v2)) := (lhs, rhs) in
  (l1 =? l2) && (c1 =? c2) && (v1 =? v2).

Module N_TTLB := OTF_to_TTLB N.
Module SortN := Sort N_TTLB.

Definition find_line_parts (xs : list sym) : list Part :=
  let f '(l, r) :=
    match (l, r) with
    | (op _ _, num id n) | (num id n, op _ _) => [(id, n)]
    | _ => []
    end in
  flat_map f (combine xs (tl xs)).

Open Scope char_scope.
Definition find_line_cogs (xs : list sym) : list Part :=
  let f '(l, r) :=
    match (l, r) with
    | (op id "*", num _ n) | (num _ n, op id "*") => [(id, n)]
    | _ => []
    end in
  flat_map f (combine xs (tl xs)).
Close Scope char_scope.

Fixpoint dedup_tl {A : Type} (eqb : A -> A -> bool) (v : A) (l : list A) :=
  match l with
  | x :: tl =>
      if eqb x v
      then dedup_tl eqb v tl
      else x :: dedup_tl eqb x tl
  | [] => []
  end.
Definition dedup {A : Type} (eqb : A -> A -> bool) (l : list A) :=
  match l with
  | x :: tl => x :: dedup_tl eqb x tl
  | [] => []
  end.
Definition find_parts (xss : list (list sym)) : list N :=
  let all_parts := flat_map find_line_parts xss in
  let all_parts_s := SortPart.sort all_parts in
  let deduped := dedup part_eqb all_parts_s in
  SortN.sort (map (fun '(_, v) => v) deduped).

Fixpoint filter_cogs_tl (id : N * N) (prev : list N) (cogs : list Part) :=
  match (cogs, prev) with
  | ([], [a; b]) => [a * b]
  | ([], _) => []
  | ((id', x) :: tl, _) =>
      if id_eqb id id'
      then filter_cogs_tl id (x :: prev) tl
      else let k := filter_cogs_tl id' [x] tl in
           match prev with
           | [a; b] => a * b :: k
           | _ => k
           end
  end.
Definition filter_cogs (cogs : list Part) : list N :=
  match cogs with
  | [] => []
  | (id, n) :: tl => filter_cogs_tl id [n] tl
  end.
Definition find_cogs (xss : list (list sym)) : list N :=
  let all_cogs := flat_map find_line_cogs xss in
  let all_cogs_s := SortPart.sort all_cogs in
  let deduped := dedup part_eqb all_cogs_s in
  filter_cogs deduped.

Definition part1 xss := fold_left N.add (find_parts (angles xss)) 0.
Definition part2 xss := fold_left N.add (find_cogs (angles xss)) 0.
Definition main (xss : list (list sym)) := (part1 xss, part2 xss).

Definition example := input
"467..114.."
"...*......"
"..35..633."
"......#..."
"617*......"
".....+.58."
"..592....."
"......755."
"...$.*...."
".664.598.."
.

Example example_parts: part1 example = 4361.
Proof. simpl. reflexivity. Qed.

Example example_cogs: part2 example = 467835.
Proof. simpl. reflexivity. Qed.
