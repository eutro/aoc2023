From Coq Require Export String List NArith ZArith Ascii Uint63.
From Coq Require Import Lia Sorting Orders OrdersEx OrdersAlt FMapAVL PArray Program.Wf.

Import IfNotations.
Export StringSyntax ListNotations.

#[global] Open Scope char_scope.
#[global] Open Scope nat_scope.
#[global] Open Scope uint63_scope.
#[global] Open Scope array_scope.

Inductive insn : Set :=
| iset : string -> int -> insn
| irem : string -> insn.

Definition uint63_of_N (n : N) := of_Z (Z.of_N n).
Definition icons (c : ascii) (i : insn) : insn :=
  match i with
  | iset s n => iset (String c s) n
  | irem s => irem (String c s)
  end.
Fixpoint parse_insn (s : string) : insn :=
  match s with
  | ""%string | "-"%string => irem ""
  | String "=" (String d EmptyString) =>
      iset "" (uint63_of_N (N_of_ascii d - N_of_ascii "0")%N)
  | String c s' =>
      let i := parse_insn s' in
      icons c i
  end.

Fixpoint hash_ (acc : int) (cs : list ascii) : int :=
  match cs with
  | [] => acc
  | c :: cs' =>
      let acc' := ((acc + (uint63_of_N (N_of_ascii c))) * 17) mod 256 in
      hash_ acc' cs'
  end.
Definition hash (s : string) : int := hash_ 0 (list_ascii_of_string s).

Example hash_HASH: hash "HASH" = 52.
Proof. reflexivity. Qed.

Definition part1 (s : list string) : int :=
  fold_left add (List.map hash s) 0.

Definition lens : Type := int * string.
Definition step_state (s : array (list lens)) (i : insn) : array (list lens) :=
  let lbl := match i with | irem s => s | iset s _ => s end in
  let has_label := fun '(_, lbl') => (lbl =? lbl')%string in
  let box := hash lbl in
  let reg := s.[box] in
  let val :=
    match i with
    | irem _ => List.filter (fun x => negb (has_label x)) reg
    | iset _ num =>
        let lens := (num, lbl) in
        if List.find has_label reg is Some _
        then List.map (fun x => if has_label x then lens else x) reg
        else lens :: reg
    end in
  s.[box <- val].

Fixpoint box_focusing_power (acc : int) (l : (list lens)) (box_idx slot : int) : int :=
  match l with
  | [] => acc
  | (fl, _) :: l' =>
      let power := (1 + box_idx) * slot * fl in
      box_focusing_power (acc + power) l' box_idx (slot + 1)
  end.
Fixpoint focusing_power_ (s : array (list lens)) (rem : nat) (i : int) (acc : int) : int :=
  match rem with
  | O => acc
  | S rem' =>
      let acc' := box_focusing_power acc (List.rev s.[i]) i 1 in
      focusing_power_ s rem' (i + 1) acc'
  end.
Definition focusing_power (s : array (list lens)) : int :=
  focusing_power_ s 256%nat 0 0.

Definition part2 (s : list string) : int :=
  let insns := List.map parse_insn s in
  let state := PArray.make 256 [] in
  let state' := fold_left step_state insns state in
  focusing_power state'.

Definition main (s : list string) :=
  (part1 s, part2 s).

Notation "'input' insn ',' .. ',' insns" :=
  (cons insn%string .. (cons insns%string nil) ..)
    (at level 200, insn at level 0, only parsing).

Definition example := input
"rn=1","cm-","qp=3","cm=2","qp-","pc=4","ot=9","ab=5","pc-","pc=6","ot=7"
.

Example sample: main example = (1320, 145).
Proof. reflexivity. Qed.
