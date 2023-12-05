From Coq Require Export String List NArith.
From Coq Require Import Lia Ascii Sorting Orders OrdersEx.

Import ListNotations.

#[global] Open Scope N_scope.

Inductive thing : Set :=
| seed | soil | fertilizer | water | light
| temperature | humidity | location.
Definition all_things : list thing :=
  [seed; soil; fertilizer; water; light; temperature; humidity; location].

Inductive range : Set :=
| range_len : N -> N -> range.
Notation "start '+=' len" :=
  (range_len start len)
    (at level 80).
Notation "start '+to' endd" :=
  (start += (endd - start))
    (at level 80).

Definition nelist (A : Type) : Type := (A * list A).
Definition nelist_to_list {A : Type} (nl : nelist A) : list A :=
  let '(x, xtl) := nl in x :: xtl.
Definition nehd {A : Type} : nelist A -> A := fst.
Notation "hd '::+' tl" :=
  (hd, (nelist_to_list tl))
    (at level 80).

Declare Custom Entry ilist.
Declare Custom Entry mappings.
Declare Custom Entry mapping.
Declare Custom Entry rmaps.
Declare Custom Entry rmap.
Notation "'input' 'seeds' ':' sl maps" :=
  (sl, maps)
    (at level 200,
      sl custom ilist at level 1,
      maps custom mappings at level 5,
      only parsing).
Notation "n .. ns" :=
  (cons n .. (cons ns nil) ..)
    (in custom ilist at level 1, n constr at level 0).
Notation "';' map ';' .. ';' maps" :=
  (cons map .. (cons maps nil) ..)
    (in custom mappings at level 5, map custom mapping at level 4).
Notation "src '-' 'to' '-' dst 'map' ':' rmapping" :=
  (src, dst, rmapping)
    (in custom mapping at level 4,
        src constr at level 0,
        dst constr at level 0,
        rmapping custom rmaps at level 2).
Notation "rmap .. rmaps" :=
  (cons rmap .. (cons rmaps nil) ..)
    (in custom rmaps at level 2, rmap custom rmap at level 1).
Notation "dst src len" :=
  (src, dst, len)
    (in custom rmap at level 1,
        src constr at level 0,
        dst constr at level 0,
        len constr at level 0).

Definition rmap : Type := list (N * N * N).
Definition thingmap : Type := thing * thing * rmap.

Definition intersect (a b : range) : option range * list range :=
  let '(astart += alen, bstart += blen) := (a, b) in
  let '(aend, bend) := (astart + alen, bstart + blen) in
  match N.compare astart bstart with
  | Lt => match N.compare aend bstart with
          | Lt | Eq => (None, [a]) (* [a a)<=[b b) *)
          | Gt => match N.compare aend bend with
                  (* [a [b a)<=b) *)
                  | Lt | Eq => (Some (bstart +to aend), [astart +to bstart])
                  (* [a [b b) a) *)
                  | Gt => (Some b, [astart +to bstart; bend +to aend])
                  end
          end
  | Eq => match N.compare aend bend with
          (* [b=[a a)<=b) *)
          | Lt | Eq => (Some a, [])
          (* [b=[a b) a) *)
          | Gt => (Some b, [bend +to aend])
          end
  | Gt => match N.compare astart bend with
          (* [b b)<=[a a)*)
          | Gt | Eq => (None, [a])
          | Lt => match N.compare aend bend with
                  (* [b [a a)<=b) *)
                  | Lt | Eq => (Some a, [])
                  (* [b [a b) a) *)
                  | Gt => (Some (astart +to bend), [bend +to aend])
                  end
          end
  end.

Definition split_count (r o : range) : N :=
  let ins := intersect r o in
  N.of_nat (length (snd ins)).
Definition Intersects (r o : range) : Prop :=
  let ins := intersect r o in
  match (fst ins) with
  | Some _ => True
  | None => False
  end.
Example test1: Intersects (1 += 1) (0 += 2).
Proof. simpl. exact I. Qed.
Example test2: ~ Intersects (1 += 1) (2 += 1).
Proof. intros F. simpl. exact F. Qed.
Example test3: Intersects (1 += 1) (1 += 1).
Proof. simpl. exact I. Qed.
Example test4: split_count (1 += 1) (1 += 1) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint lookup (rm : rmap) (np : range) : list range :=
  match rm with
  | [] => [np]
  | (src, dst, len) :: rmtl =>
      match intersect np (src += len) with
      | (None, rem) => flat_map (lookup rmtl) rem
      | (Some (start += len), rem) =>
          ((dst + (start - src)) += len) :: flat_map (lookup rmtl) rem
      end
  end.
Definition lookup_m (rm : rmap) : list range -> list range :=
  List.flat_map (lookup rm).

Definition thing_eqb (l r : thing) : bool :=
  match (l, r) with
  | (seed, seed) | (soil, soil) | (fertilizer, fertilizer)
  | (water, water) | (light, light) | (temperature, temperature)
  | (humidity, humidity) | (location, location) => true
  | _ => false
  end.
Definition thingpair_eqb (l r : thing * thing) : bool :=
  thing_eqb (fst l) (fst r) && thing_eqb (snd l) (snd r).

Fixpoint assoc {A B : Type} (eqb : A -> A -> bool) (dflt : B) (l : list (A * B)) (to_find : A) : B :=
  match l with
  | [] => dflt
  | (k, v) :: ltl =>
      if eqb k to_find then v
      else assoc eqb dflt ltl to_find
  end.

Fixpoint compose_l_ {A : Type} (funs : list (A -> A)) (x : A) : A :=
  match funs with
  | [] => x
  | g :: fs => compose_l_ fs (g x)
  end.
Definition compose_l {A : Type} (funs : list (A -> A)) : A -> A :=
  compose_l_ funs.

Definition compose_pipeline (tm : list thingmap) (path : list thing) : list range -> list range :=
  let rmaps := List.map (assoc thingpair_eqb [] tm) (combine path (tl path)) in
  let funs := List.map lookup_m rmaps in
  compose_l funs.

Definition inty : Type := list N * list thingmap.

Definition part1_ranges (seeds : list N) : list range :=
  List.map (fun s => s += 1) seeds.
Fixpoint part2_ranges (seeds : list N) : list range :=
  match seeds with
  | src::len::stl => (src += len) :: part2_ranges stl
  | _ => []
  end.

Definition solve_with_pipeline (get_ranges : list N -> list range) (inp : inty) : list range :=
  let pipeline := compose_pipeline (snd inp) all_things in
  let seeds := get_ranges (fst inp) in
  pipeline seeds.

Definition find_min_loc (l : list range) : N :=
  let starts := List.map (fun '(x += _) => x) l in
  fold_left N.min (tl starts) (hd 0 starts).

Definition main (inp : inty) :=
  let s f := find_min_loc (solve_with_pipeline f inp) in
  (s part1_ranges, s part2_ranges).

Definition example := input
seeds: 79 14 55 13

; seed-to-soil map:
50 98 2
52 50 48

; soil-to-fertilizer map:
0 15 37
37 52 2
39 0 15

; fertilizer-to-water map:
49 53 8
0 11 42
42 0 7
57 7 4

; water-to-light map:
88 18 7
18 25 70

; light-to-temperature map:
45 77 23
81 45 19
68 64 13

; temperature-to-humidity map:
0 69 1
1 0 69

; humidity-to-location map:
60 56 37
56 93 4
.

Compute main example.
