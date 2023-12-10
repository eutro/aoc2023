From Coq Require Export String List NArith Ascii.
From Coq Require Import Lia Sorting Orders OrdersEx OrdersAlt FMapAVL.

Import IfNotations.
Export ListNotations.

#[global] Open Scope char_scope.
#[global] Open Scope nat_scope.
#[global] Open Scope N_scope.

Definition node : Type := ascii * ascii * ascii.
Definition node_of_string (s : string) : node :=
  match list_ascii_of_string s with
  | [a;b;c] => (a,b,c)
  | _ => (".",".",".")
  end.
Definition node_ends_with (c : ascii) (n : node) : bool :=
  let '(_, _, v) := n in Ascii.eqb c v.
Definition node_startb := node_ends_with "A".
Definition node_endb := node_ends_with "Z".

Inductive direction : Set := Left | Right.
Definition direction_of_ascii (c : ascii) : direction :=
  match c with
  | "L" => Left
  | _ => Right
  end.
Definition directions_of_string (s : string) : list direction :=
  List.map direction_of_ascii (list_ascii_of_string s).

Module NodeOrder <: OrderedTypeFull.
  Module PO_A_A := PairOrderedType Ascii_as_OT Ascii_as_OT.
  Module PO_A_A_A := PairOrderedType PO_A_A Ascii_as_OT.
  Module PO_Full := OT_to_Full PO_A_A_A.
  Include PO_Full.
  Definition eqb (a b : t) : bool :=
    if compare a b is Eq then true else false.
End NodeOrder.

Module BackportNodeOrder := Backport_OT NodeOrder.
Module NodeMap := FMapAVL.Make (BackportNodeOrder).

Definition node_map : Type := NodeMap.t (node * node).

Definition build_map (nodes : list (node * (node * node))) : node_map :=
  fold_left
    (fun m '(root, (lhs, rhs)) =>
       NodeMap.add root (lhs, rhs) m)
    nodes
    (NodeMap.empty (node * node)).

Definition step_node (m : node_map) (n : node) (d : direction) : option node :=
  match NodeMap.find n m with
  | Some (l, r) => Some (if d is Left then l else r)
  | None => None
  end.

Inductive success : Set := Ok | OutOfFuel | MissingNode.
Definition unwrap_success {A : Type} (s : success * A) : option A :=
  match s with
  | (Ok, x) => Some x
  | _ => None
  end.
Fixpoint step_until_
  (m : node_map) (target : node -> bool) (all_insns : list direction)
  (fuel : nat) (insns : list direction)
  (trail : list node) (src : node) : success * (list node * list direction) :=
  let trail' := src::trail in
  match fuel with
  | O => (OutOfFuel, (trail, insns))
  | S fuel' =>
      let (dir, insns') :=
        match insns with
        | [] => (hd Left all_insns, tl all_insns)
        | d::i' => (d, i')
        end in
      match step_node m src dir with
      | Some src' =>
          if target src' then (Ok, (src'::trail', insns')) else
            step_until_ m target all_insns
              fuel' insns' trail' src'
      | None => (MissingNode, (trail', insns'))
      end
    end.
Definition step_until m dst src insns fuel :=
  step_until_ m dst insns fuel insns [] src.

Definition find_loop m insns fuel src : N :=
  match unwrap_success (step_until m node_endb src insns fuel) with
  | Some (looper::trail_butfirst as trail, remaining_insns) =>
      (* the input makes this too easy, further loops happen to be the
         same length, and no other terminals are reached *)
      N.of_nat (List.length trail_butfirst) (*
      match (unwrap_success (step_until_ m (NodeOrder.eqb looper) insns
                               fuel remaining_insns [] looper)) with
      | Some (_::loop_butfirst, remaining_insns2) =>
          Some (trail_butfirst, loop_butfirst)
      | _ => None
      end *)
  | _ => 0
  end.

#[global] Open Scope string_scope.

Definition default_fuel : nat := 100000.

Definition part1 (inp : list direction * node_map) :=
  let '(success, (path, _)) :=
    step_until (snd inp)
      (NodeOrder.eqb (node_of_string "ZZZ"))
      (node_of_string "AAA")
      (fst inp)
      default_fuel in
  unwrap_success (success, N.of_nat (List.length path) - 1).

Definition part2 (inp : list direction * node_map) :=
  let all_nodes := List.map fst (NodeMap.elements (snd inp)) in
  let starts := List.filter node_startb all_nodes in
  let loops := List.map (find_loop (snd inp) (fst inp) default_fuel) starts in
  List.fold_left N.lcm loops 1.

Definition main inp := (part1 inp, part2 inp).

Declare Custom Entry node.
Notation "'input' directions node .. nodes" :=
  (directions_of_string directions, build_map (cons node .. (cons nodes nil) ..))
    (at level 200, directions at level 0, node custom node at level 2, only parsing).
Notation "root '=' '(' lhs ',' rhs ')'" :=
  (node_of_string root, (node_of_string lhs, node_of_string rhs))
    (in custom node at level 2, root constr at level 0, lhs constr at level 0, rhs constr at level 0).

Definition example1 := input
"RL"

"AAA" = ("BBB", "CCC")
"BBB" = ("DDD", "EEE")
"CCC" = ("ZZZ", "GGG")
"DDD" = ("DDD", "DDD")
"EEE" = ("EEE", "EEE")
"GGG" = ("GGG", "GGG")
"ZZZ" = ("ZZZ", "ZZZ")
.

Definition example2 := input
"LLR"

"AAA" = ("BBB", "BBB")
"BBB" = ("AAA", "ZZZ")
"ZZZ" = ("ZZZ", "ZZZ")
.

Compute part1 example1.
Compute part1 example2.
