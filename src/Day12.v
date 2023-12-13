From Coq Require Export String List NArith Ascii.
From Coq Require Import Lia Sorting Orders OrdersEx OrdersAlt FMapAVL Program.Wf.

Import IfNotations.
Export StringSyntax ListNotations.

#[global] Open Scope char_scope.
#[global] Open Scope nat_scope.
#[global] Open Scope N_scope.

Inductive status : Set :=
| Operational | Damaged | Unknown.
Inductive spring_rec : Type :=
  mkrec : list status -> list N -> spring_rec.

Definition status_of_ascii (c : ascii) : status :=
  match c with
  | "#" => Damaged
  | "." => Operational
  | _ => Unknown
  end.
Definition statuses_of_string (s : string) : list status :=
  List.map status_of_ascii (list_ascii_of_string s).

Fixpoint head_matches_ (i : nat) (s : list status) (g : nat) : option nat :=
  match (g, s) with
  | (S g', (Damaged | Unknown) :: s') => head_matches_ (S i) s' g'
  | (S _, (Operational :: _ | [])) => None
  | (O, (Operational | Unknown) :: _) => Some (S i)
  | (O, []) => Some i
  | (O, Damaged :: _) => None
  end.
Definition head_matches := head_matches_ O.
Definition get_valid_steps (s : list status) (gs : list N) : list (option nat) :=
  List.map (fun g => head_matches s (N.to_nat g)) gs.

Fixpoint count_valid_groupings_ (s : list status) (gs : list N) : list (list N) :=
  match s with
  | [] => [List.map (fun _ => 0) gs ++ [1]]
  | fc::s' =>
      let dp := count_valid_groupings_ s' gs in
      let next_col := List.hd [] dp in
      let is_damaged := if fc is Damaged then true else false in
      let next_can_be_empty := List.last next_col 0 =? 1 in
      let tl_can_be_empty := if negb is_damaged && next_can_be_empty then 1 else 0 in
      let valid_steps := get_valid_steps s gs in
      let step_all :=
        List.fold_left
          (fun '(acc, i) is_valid =>
             let next_cnt :=
               if is_damaged then 0 (* we cannot just ignore it *)
               else nth i next_col 0 in
             let skip_cnt :=
               match is_valid with
               | None => 0
               | Some len =>
                   let skip_col := nth (pred len) dp [] in
                   nth (S i) skip_col 0
               end in
             (next_cnt + skip_cnt :: acc, S i))
          valid_steps
          ([], O)
      in
      List.rev (tl_can_be_empty :: fst step_all) :: dp
  end.
Definition count_valid_groupings (r : spring_rec) :=
  let '(mkrec s gs) := r in
  let all_groupings := count_valid_groupings_ s gs in
  hd 0 (hd [] all_groupings).

Definition unfold_rec (r : spring_rec) : spring_rec :=
  let '(mkrec s gs) := r in
  let s' := List.tl (flat_map id (List.repeat (Unknown :: s) 5)) in
  let gs' := flat_map id (List.repeat gs 5) in
  mkrec s' gs'.

Definition part (f : spring_rec -> spring_rec) (inp : list spring_rec) :=
  let mapped := List.map f inp in
  let groupings := List.map count_valid_groupings mapped in
  List.fold_left N.add groupings 0.

Definition main (inp : list spring_rec) :=
  (part id inp, part unfold_rec inp).

Declare Custom Entry record.
Declare Custom Entry groups.
Notation "'input' record .. records" :=
  (cons record .. (cons records nil) ..)
    (at level 200, record custom record at level 2, only parsing).
Notation "conds groups" :=
  (mkrec (statuses_of_string conds) groups)
    (in custom record at level 2, conds constr at level 1, groups custom groups at level 1).
Notation "g ',' .. ',' gs" :=
  (cons g .. (cons gs nil) ..)
    (in custom groups at level 1, g constr at level 1).

Definition example := input
"???.###" 1,1,3
".??..??...?##." 1,1,3
"?#?#?#?#?#?#?#?" 1,3,1,6
"????.#...#..." 4,1,1
"????.######..#####." 1,6,5
"?###????????" 3,2,1
.

Example sample: main example = (21, 525152).
Proof. reflexivity. Qed.
