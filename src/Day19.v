From Coq Require Export String List NArith ZArith Ascii Uint63.
From Coq Require Import Lia Sorting Orders OrdersEx OrdersAlt FMapAVL PArray Program.Wf.
From Aoc2023 Require Import OrderUtils.

Import IfNotations.
Export StringSyntax ListNotations.

#[global] Open Scope char_scope.
#[global] Open Scope uint63_scope.
#[global] Open Scope array_scope.

Inductive part_of (T : Type) : Type :=
  mkPart { part_x : T ; part_m : T ; part_a : T ; part_s : T }.
Inductive part_field : Set := px | pm | pa | ps.
Inductive range : Set := mkRange { rStart : int ; rEnd : int }.
Arguments part_x {T} _. Arguments part_m {T} _.
Arguments part_a {T} _. Arguments part_s {T} _.

Definition get_field {A : Type} (f : part_field) (p : part_of A) : A :=
  match f with px => part_x | pm => part_m | pa => part_a | ps => part_s end p.
Definition set_field {A : Type} (f : part_field) (p : part_of A) (v : A) : part_of A :=
  match f with
  | px => mkPart A v (part_m p) (part_a p) (part_s p)
  | pm => mkPart A (part_x p) v (part_a p) (part_s p)
  | pa => mkPart A (part_x p) (part_m p) v (part_s p)
  | ps => mkPart A (part_x p) (part_m p) (part_a p) v
  end.

Definition part : Set := part_of int.
Definition rpart : Set := part_of range.

Inductive terminal_workflow : Set :=
| Ref : string -> terminal_workflow | Accept | Reject.
Inductive workflow : Type :=
| Cond : part_field -> comparison -> int -> workflow -> workflow -> workflow
| Terminal : terminal_workflow -> workflow.

Module Backport_StringOrder := Backport_OT String_as_OT.
Module StringMap := FMapAVL.Make Backport_StringOrder.
Definition workflow_map : Type := StringMap.t workflow.

Definition build_map (entries : list (string * workflow)) : workflow_map :=
  fold_left
    (fun m '(k, v) => StringMap.add k v m)
    entries (StringMap.empty workflow).

Definition inp_ty : Type := workflow_map * list part.

Definition compare_eqb (a b : comparison) : bool :=
  match (a, b) with
  | (Eq, Eq) | (Lt, Lt) | (Gt, Gt) => true
  | _ => false
  end.

Section Run.
  Variables (m : workflow_map).

  Definition do_workflow {A : Type} {Of : Type}
    (f : workflow -> part_of Of -> A)
    (dflt : A) (wf : string) (p : part_of Of) : A :=
    match StringMap.find wf m with
    | Some flow => f flow p
    | None => dflt
    end.

  Fixpoint run_workflow1 (flow : workflow) (p : part) : terminal_workflow :=
    match flow with
    | Terminal t => t
    | Cond field cmp num thn els =>
        if compare_eqb (compare (get_field field p) num) cmp
        then run_workflow1 thn p
        else run_workflow1 els p
    end.
  Fixpoint run_workflow (fuel : nat) (wf : string) (p : part) : bool :=
    match fuel with
    | O => false
    | S fuel' =>
        match do_workflow run_workflow1 Reject wf p with
        | Ref nxt => run_workflow fuel' nxt p
        | Accept => true
        | Reject => false
        end
    end.

  Definition validate_range (r : range) : option range :=
    if rEnd r <? rStart r then None else Some r.
  Definition split_range (r : range) (cmp : comparison) (n : int) : option range * option range :=
    let include_lt := if cmp is Gt then true else false in
    let lhs := mkRange (rStart r) (if include_lt then n else n - 1) in
    let rhs := mkRange (if include_lt then n + 1 else n) (rEnd r) in
    if cmp is Lt
    then (validate_range lhs, validate_range rhs)
    else (validate_range rhs, validate_range lhs).

  Fixpoint compile_workflow1 (flow : workflow) (p : rpart) : list (terminal_workflow * rpart) :=
    match flow with
    | Terminal t => [(t, p)]
    | Cond field cmp num thn els =>
        let '(trues, falses) := split_range (get_field field p) cmp num in
        let tail '(w, x) :=
          match x with
          | None => []
          | Some x => compile_workflow1 w (set_field field p x)
          end in
        flat_map tail [(thn, trues); (els, falses)]
    end.
  Fixpoint compile_workflow (fuel : nat) (wf : string) (p : rpart) : list rpart :=
    match fuel with
    | O => []
    | S fuel' =>
        let tail p :=
          match p with
          | (Reject, _) => []
          | (Accept, x) => [x]
          | (Ref nxt, x) => compile_workflow fuel' nxt x
          end in
        flat_map tail (do_workflow compile_workflow1 [] wf p)
    end.

End Run.

Definition part_rating (p : part) : int :=
  part_x p + part_m p + part_a p + part_s p.

Definition range_span (r : range) := rEnd r + 1 - rStart r.
Definition rpart_count (p : rpart) : int :=
  range_span (part_x p) * range_span (part_m p) *
    range_span (part_a p) * range_span (part_s p).

Definition part1 (i : inp_ty) :=
  let '(m, parts) := i in
  let accepted := filter (run_workflow m (StringMap.cardinal m) "in") parts in
  fold_left add (map part_rating accepted) 0.

Definition part2 (i : inp_ty) :=
  let '(m, _) := i in
  let max_range := mkRange 1 4000 in
  let top_part := mkPart range max_range max_range max_range max_range in
  let accepted := compile_workflow m (StringMap.cardinal m) "in" top_part in
  fold_left add (map rpart_count accepted) 0.

Definition main (i : inp_ty) := (part1 i, part2 i).

Declare Custom Entry workflow0.
Declare Custom Entry workflow.
Declare Custom Entry field.
Declare Custom Entry order.
Declare Custom Entry part.
Notation "'input' workflow .. workflows ';' part .. parts" :=
  (build_map (cons workflow .. (cons workflows nil) ..),
    (cons part .. (cons parts nil) ..))
  (at level 200, workflow at level 200, part custom part at level 200).

Notation "{ 'x' = x , 'm' = m , 'a' = a , 's' = s }" :=
  (mkPart int x%uint63 m%uint63 a%uint63 s%uint63)
    (in custom part at level 200,
        x constr at level 0, m constr at level 0,
        a constr at level 0, s constr at level 0).

Notation "'wf' nm workflow" :=
  (nm%string, workflow)
    (at level 200,
      nm at level 0,
      workflow custom workflow0 at level 200).

Notation "{ workflow }" :=
  workflow (in custom workflow0 at level 200, workflow custom workflow at level 3).
Notation "field order num ':' thn ',' els" :=
  (Cond field order num%uint63 thn els)
    (in custom workflow at level 3,
        num constr at level 0, field custom field at level 0,
        order custom order at level 0,
        thn at level 3, els at level 3).
Notation "'R'" := (Terminal Reject) (in custom workflow at level 3).
Notation "'A'" := (Terminal Accept) (in custom workflow at level 3).
Notation "'wf' ref" := (Terminal (Ref ref%string)) (in custom workflow at level 3, ref constr at level 0).

Notation "'<'" := Lt (in custom order).
Notation "'>'" := Gt (in custom order).

Notation "'x'" := px (in custom field).
Notation "'m'" := pm (in custom field).
Notation "'a'" := pa (in custom field).
Notation "'s'" := ps (in custom field).

Definition example := input
wf"px"{a<2006:wf"qkq",m>2090:A,wf"rfg"}
wf"pv"{a>1716:R,A}
wf"lnx"{m>1548:A,A}
wf"rfg"{s<537:wf"gd",x>2440:R,A}
wf"qs"{s>3448:A,wf"lnx"}
wf"qkq"{x<1416:A,wf"crn"}
wf"crn"{x>2662:A,R}
wf"in"{s<1351:wf"px",wf"qqz"}
wf"qqz"{s>2770:wf"qs",m<1801:wf"hdj",R}
wf"gd"{a>3333:R,R}
wf"hdj"{m>838:A,wf"pv"}
;
{x=787,m=2655,a=1222,s=2876}
{x=1679,m=44,a=2067,s=496}
{x=2036,m=264,a=79,s=2244}
{x=2461,m=1339,a=466,s=291}
{x=2127,m=1623,a=2188,s=1013}
.

Example sample: main example = (19114, 167409079868000).
Proof. reflexivity. Qed.
