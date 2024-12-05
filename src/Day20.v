From Coq Require Export String List NArith ZArith Ascii Uint63.
From Coq Require Import Lia Sorting Orders OrdersEx OrdersAlt FMapAVL PArray Program.Wf.
From Aoc2023 Require Import OrderUtils.

Import IfNotations.
Export StringSyntax ListNotations PArrayNotations.

#[global] Open Scope string_scope.
#[global] Open Scope uint63_scope.
#[global] Open Scope array_scope.

Definition of_nat (n : nat) := of_Z (Z.of_nat n).
Definition of_N (n : N) := of_Z (Z.of_N n).
Definition to_nat (i : int) := Z.to_nat (to_Z i).
Definition to_N (i : int) := Z.to_N (to_Z i).

Inductive module_type : Set := flipflop | conj | broadcast | broken.
Inductive module_decl :=
  mkDecl { declTy : module_type
         ; declName : string
         ; declOuts : list string }.

Module Backport_StringOrder := Backport_OT String_as_OT.
Module StringMap := FMapAVL.Make Backport_StringOrder.
Import StringMap.

Inductive node :=
  mkNode { nId : int
         ; nName : string
         ; nTy : module_type
         ; nInps : list int
         ; nOuts : list int }.
Definition add_inp (i : int) (n : node) :=
  let '(mkNode id nm ty inps outs) := n in
  mkNode id nm ty (i :: inps) outs.
Definition add_out (o : int) (n : node) :=
  let '(mkNode id nm ty inps outs) := n in
  mkNode id nm ty inps (o :: outs).
Definition default_node :=
  {| nId := 0
  ; nName := "default"
  ; nTy := broken
  ; nInps := []
  ; nOuts := [] |}.

Definition module_graph : Type := array node.
Inductive module_state : Set :=
| stateless | sFlipflop : bool -> module_state | sConj : int -> module_state.
Definition run_state : Type := array module_state.

Definition flipFF (s : module_state) : module_state * bool :=
  let b :=
    match s with
    | sFlipflop true => false
    | _ => true
    end in
  (sFlipflop b, b).
Fixpoint indexof (i : int) (inp : int) (inps : list int) : int :=
  match inps with
  | [] => i
  | x :: inps' =>
      if inp =? x
      then i
      else indexof (i + 1) inp inps'
  end.
Definition check_conj (s : module_state) (inps : list int) (inp : int) (sig : bool)
  : module_state * bool :=
  let mask := (1 << of_nat (List.length inps)) - 1 in
  let idx := indexof 0 inp inps in
  let old :=
    match s with
    | sConj m => m
    | _ => 0
    end in
  let new := set_digit old idx sig in
  (sConj new, negb (new land mask =? mask)).

Definition init_state (g : module_graph) : run_state :=
  make (length g) stateless.

Fixpoint cc_rec (graph : module_graph)
  (decls : StringMap.t module_decl)
  (ids : StringMap.t int)
  (nid : int)
  (q : list (string * option int))
  (rem : nat) : module_graph * bool :=
  (fix resolve_hd graph q : module_graph * bool :=
     match q with
     | [] => (graph, true)
     | (name, input) :: q' =>
         match find name ids with
             | None =>
                 match (find name decls, rem) with
                 | (_, O) => (graph, false)
                 | (None, _) =>
                     let graph' :=
                       match input with
                       | None => graph
                       | Some inp_id => graph.[inp_id <- add_out 9999 graph.[inp_id]]
                       end in
                     resolve_hd graph' q'
                 | (Some decl, S rem') =>
                     let node :=
                       {| nId := nid
                       ; nName := declName decl
                       ; nTy := declTy decl
                       ; nInps :=
                           match input with
                           | None => []
                           | Some n => [n]
                           end
                       ; nOuts := [] |} in
                     let graph' := graph.[nid <- node] in
                     let graph'' :=
                       match input with
                       | None => graph'
                       | Some inp_id => graph'.[inp_id <- add_out nid graph'.[inp_id]]
                       end in
                     let ids' := add (declName decl) nid ids in
                     let nid' := nid + 1 in
                     let q_extra := List.map (fun nm => (nm, Some nid)) (declOuts decl) in
                     cc_rec graph'' decls ids' nid' (q' ++ q_extra) rem'
                 end
             | Some node_id =>
                 let graph' :=
                   match input with
                   | None => graph
                   | Some inp_id =>
                       let graph' := graph.[node_id <- add_inp inp_id graph.[node_id]] in
                       let graph'' := graph'.[inp_id <- add_out node_id graph'.[inp_id]] in
                       graph''
                   end in
                 resolve_hd graph' q'
             end
     end)
    graph q.

Definition cc_graph (decls : list module_decl) : module_graph * bool :=
  let named_decls :=
    fold_left
      (fun acc decl =>
         add (declName decl) decl acc)
      decls (empty module_decl) in
  let graph := PArray.make (of_nat (List.length decls)) default_node in
  let ids := empty int in
  cc_rec graph named_decls ids 0 [("broadcaster", None)] 1000%nat.

Inductive fqueue (T : Type) :=
  mkQ { qFront : list T ; qBack : list T }.
Arguments mkQ {T}.
Definition dequeue {T : Type} (fq : fqueue T) : option T * fqueue T :=
  match fq with
  | mkQ (elt::front') back => (Some elt, mkQ front' back)
  | mkQ [] [] => (None, fq)
  | mkQ [] back =>
      match List.rev back with
      | elt::front' => (Some elt, mkQ front' [])
      | [] => (None, fq)
      end
  end.
Definition enqueue {T : Type} (fq : fqueue T) (elts : list T) : fqueue T :=
  mkQ (qFront T fq) (elts ++ qBack T fq).

Definition update_count (c : int * int) (sig : bool) : int * int :=
  let '(lo, hi) := c in
  if sig
  then (lo, hi + 1)
  else (lo + 1, hi).

Definition pulse_signal (s : run_state) (n : node) (src : int) (sig : bool) :=
  match (nTy n, sig) with
  | (broken, _) => (s, None)
  | (flipflop, true) => (s, None)
  | (flipflop, false) =>
      let (ls', out) := flipFF s.[nId n] in
      let s' := s.[nId n <- ls'] in
      (s', Some out)
  | (conj, _) =>
      let (ls', out) := check_conj s.[nId n] (nInps n) src sig in
      let s' := s.[nId n <- ls'] in
      (s', Some out)
  | (broadcast, sig) => (s, Some sig)
  end.

Definition signal : Type := int * int * bool.

Definition step_counts (s : signal) (c : int * int) : int * int :=
  let '(_, _, sig) := s in
  update_count c sig.
Definition pulse_log : Type := list signal.
Definition log_pulses := cons (A:=signal).

Section Sim.
  Variable g : module_graph.
  Variables (Aux : Type) (update_aux : signal -> Aux -> Aux).

  Fixpoint run_signals
    (s : run_state)
    (fuel : nat) (aux : Aux) (q : fqueue signal)
    : run_state * Aux * bool (* success *) :=
    match (fuel, dequeue q) with
    | (O, _) => (s, aux, false)
    | (_, (None, _)) => (s, aux, true)
    | (S fuel', (Some ((src, dst, sig) as psig), q')) =>
        let aux' := update_aux psig aux in
        let '(s', pulsed) := pulse_signal s g.[dst] src sig in
        let q'' :=
          match pulsed with
          | None => q'
          | Some pulse =>
              let pulses :=
                List.map
                  (fun pulse_dst => (dst, pulse_dst, pulse))
                  (nOuts g.[dst]) in
              enqueue q' pulses
          end in
        run_signals s' fuel' aux' q''
    end.

  Definition push_button (sc : run_state * Aux)
    : run_state * Aux * bool :=
    let '(s, aux) := sc in
    run_signals
      s (1000%nat) aux
      (mkQ [(0, 0, false)] []).

End Sim.

Definition part1 (d : list module_decl) :=
  let g := fst (cc_graph d) in
  let '(_, (x, y)) :=
    N.recursion
      (init_state g, (0, 0))
      (fun _ sc => fst (push_button g (int * int) step_counts sc))
      1000%N in
  x * y.

Definition main (d : list module_decl) := (part1 d, cc_graph d).

Declare Custom Entry decl.
Declare Custom Entry node.
Declare Custom Entry declTy.
Declare Custom Entry nodeList.
Notation "'input' decl .. decls" :=
  (cons decl .. (cons decls nil) ..)
    (at level 200, decl custom decl,
      format "'input' '//' decl '//' .. '//' decls").
Notation "'mDecl' decl" :=
  decl (at level 200, decl custom decl).
Notation "'mNode' node" :=
  node (at level 200, node custom node).

Notation "'%'" := flipflop (in custom declTy at level 200).
Notation "'&'" := conj (in custom declTy at level 200).
Notation "'!'" := broken (in custom declTy at level 200).
Notation "" := broadcast (in custom declTy at level 200).

Notation "ty name '->' out ',' .. ',' outs" :=
  (mkDecl ty name
     (cons out%string .. (cons outs%string nil) ..))
    (in custom decl at level 200,
        ty custom declTy,
        name constr at level 0,
        out constr at level 0,
        format "ty name  '->'  out ','  .. ','  outs").

Notation "" := nil (in custom nodeList).
Notation "x , .. , xs" :=
  (cons x .. (cons xs nil) ..)
    (in custom nodeList at level 200, x constr at level 0).

Notation "ty name ( id ) , 'inputs' ( inps ) , 'outputs' ( outs )" :=
  (mkNode id%uint63 name%string ty inps outs)
    (in custom node at level 200,
        ty custom declTy,
        id constr at level 0,
        name constr at level 0,
        inps custom nodeList at level 200,
        outs custom nodeList at level 200,
        format "'[' ty name ( id ) ,  '[' 'inputs' ( '[hv ' inps ']' ) ']' ,  '[' 'outputs' ( '[hv ' outs ']' ) ']' ']'").

Definition example1 := input
"broadcaster" -> "a", "b", "c"
%"a" -> "b"
%"b" -> "c"
%"c" -> "inv"
&"inv" -> "a"
.

Definition example2 := input
"broadcaster" -> "a"
%"a" -> "inv", "con"
&"inv" -> "b"
%"b" -> "con"
&"con" -> "output"
.

Compute part1 example2.
