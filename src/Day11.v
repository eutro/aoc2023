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

Module Backport_N := Backport_OT N.
Module IntMap := FMapAVL.Make Backport_N.
Definition int_set : Type := IntMap.t unit.
Definition int_psum : Type := IntMap.t N.

Definition inp_grid : Type := PosnMap.t unit.
Fixpoint build_row (m : inp_grid) (row col : N) (chars : list ascii) : inp_grid :=
  match chars with
  | [] => m
  | c :: chars' =>
      let m' := if c is "." then m
                else PosnMap.add (row, col) tt m in
      build_row m' row (N.succ col) chars'
  end.
Fixpoint build_map_ (m : inp_grid) (row : N) (ls : list string) : inp_grid :=
  match ls with
  | [] => m
  | row_s :: ls' =>
      let m' := build_row m row 0 (list_ascii_of_string row_s) in
      build_map_ m' (N.succ row) ls'
  end.
Definition build_map (ls : list string) : inp_grid :=
  build_map_ (PosnMap.empty unit) 0 ls.

Fixpoint find_minmax_ (mn mx : posn) (ps : list posn) : posn * posn :=
  let '((mn_x, mn_y), (mx_x, mx_y)) := (mn, mx) in
  match ps with
  | (x, y) :: ps' => find_minmax_ (N.min x mn_x, N.min y mn_y) (N.max x mx_x, N.max y mx_y) ps'
  | [] => (mn, mx)
  end.
Definition find_minmax (ps : list posn) : posn * posn :=
  match ps with
  | p :: ps' => find_minmax_ p p ps'
  | [] => ((0, 0), (0, 0))
  end.

Fixpoint range_fold_ {A : Type} (f : A -> N -> A) (x : N) (rem : nat) (acc : A) : A :=
  match rem with
  | O => acc
  | S rem' => range_fold_ f (N.succ x) rem' (f acc x)
  end.

Definition minmax (a b : N) : N * N := (N.min a b, N.max a b).
Definition range_fold {A : Type} (f : A -> N -> A) (lhs rhs : N) (i : A) : A :=
  let '(mn, mx) := minmax lhs rhs in
  range_fold_ f mn (N.to_nat (mx + 1 - mn)) i.

Definition psum_range (ints : int_set) (mn mx : N) : int_psum :=
  fst (range_fold
         (fun '(ip, sum) x =>
            let sum' := if IntMap.mem x ints then sum else sum + 1 in
            (IntMap.add x sum ip, sum'))
         mn mx
         (IntMap.empty N, 0)).

Definition count_between (ints : int_set) (lhs rhs : N) : N :=
  range_fold (fun x i => if IntMap.mem x ints then x else x + 1) lhs rhs 0.
Definition psum_between (psum : int_psum) (lhs rhs : N) : N :=
  let '(mn, mx) := minmax lhs rhs in
  match (IntMap.find mn psum, IntMap.find mx psum) with
  | (Some mnv, Some mxv) => mxv - mnv
  | _ => 0
  end.

Definition find_nonempty (inp : inp_grid) : int_psum * int_psum :=
  let as_sets :=
    PosnMap.fold
      (fun '(x, y) _ '(xs, ys) =>
         (IntMap.add x tt xs,
           IntMap.add y tt ys))
      inp (IntMap.empty unit, IntMap.empty unit) in
  let '((mn_x, mn_y), (mx_x, mx_y)) :=
    find_minmax (List.map fst (PosnMap.elements inp)) in
  (psum_range (fst as_sets) mn_x mx_x,
   psum_range (snd as_sets) mn_y mx_y).

Section CountDists.
  Variable growth : N.

  Definition dist_between (nonempties : int_psum * int_psum) (lhs rhs : posn) : N :=
    let f (side : forall A, A * A -> A) :=
      let lp := side N lhs in
      let rp := side N rhs in
      let psum := side int_psum nonempties in
      let '(mn_p, mx_p) := if rp <? lp then (rp, lp) else (lp, rp) in
      let find_psum p := match IntMap.find p psum with Some x => x | None => 0 end in
      (find_psum mx_p - find_psum mn_p) * (N.pred growth) + (mx_p - mn_p) in
    f (fun _ => fst) + f (fun _ => snd).

  Fixpoint all_dists_between1 (acc : N) (nonempties : int_psum * int_psum) (first_elt : posn) (elts : list posn) : N :=
    match elts with
    | [] => acc
    | elt :: elts' => all_dists_between1 (acc + dist_between nonempties first_elt elt) nonempties first_elt elts'
    end.
  Fixpoint all_dists_between0 (acc : N) (nonempties : int_psum * int_psum) (elts : list posn) : N :=
    match elts with
    | [] => acc
    | elt :: elts' => all_dists_between0 (all_dists_between1 acc nonempties elt elts') nonempties elts'
    end.
  Definition all_dists_between (inp : inp_grid) : N :=
    all_dists_between0 0 (find_nonempty inp) (List.map fst (PosnMap.elements inp)).
End CountDists.

Definition main (inp : inp_grid) :=
  (all_dists_between 2 inp,
   all_dists_between 1000000 inp).

Notation "'input' line .. lines" :=
  (build_map (cons line .. (cons lines nil) ..))
    (at level 200, line at level 0, only parsing).

#[global] Open Scope string_scope.

Definition example := input
"...#......"
".......#.."
"#........."
".........."
"......#..."
".#........"
".........#"
".........."
".......#.."
"#...#....."
.

Example sample1: all_dists_between 2 example = 374.
Proof. reflexivity. Qed.
Example sample2: List.map (fun i => all_dists_between i example) [10; 100] = [1030; 8410].
Proof. reflexivity. Qed.
