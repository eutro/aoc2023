From Coq Require Export String List NArith.
From Coq Require Import Lia Ascii Sorting Orders OrdersEx OrdersAlt Init.Byte.

Export ListNotations.
Import IfNotations.
Import StringSyntax.

#[global] Open Scope byte_scope.
#[global] Open Scope N_scope.

Module Type Mapper (Src Dst : Typ).
  Parameter map : Src.t -> Dst.t.
End Mapper.
Module OrderByFun (Src : Typ) (Dst : OrderedTypeAlt) (M : Mapper Src Dst).
  Definition t : Type := Src.t.

  Definition compare (l r : t) : comparison :=
    Dst.compare (M.map l) (M.map r).

  Infix "?=" := compare (at level 70, no associativity).

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof. intros x y. apply Dst.compare_sym. Qed.
  Lemma compare_trans : forall c x y z, (x ?= y) = c -> (y ?= z) = c -> (x ?= z) = c.
  Proof. intros c x y z. apply Dst.compare_trans. Qed.
End OrderByFun.

Module Card.
  Inductive card : Set :=
  |CA|CK|CQ|CJ|CT|C9|C8|C7|C6|C5|C4|C3|C2.
  Definition t : Type := card.

  Definition map {A B : Type} (m : card -> A) (f : A -> B -> B) (i : B) :=
    (f (m CJ)
       (f (m CK)
          (f (m CQ)
             (f (m CA)
                (f (m CT)
                   (f (m C9)
                      (f (m C8)
                         (f (m C7)
                            (f (m C6)
                               (f (m C5)
                                  (f (m C4)
                                     (f (m C3)
                                        (f (m C2)
                                           i))))))))))))).

  Definition card_of_byte (b : byte) : card :=
    match b with
    | "A" => CA | "K" => CK | "Q" => CQ | "J" => CJ | "T" => CT
    | "9" => C9 | "8" => C8 | "7" => C7 | "6" => C6
    | "5" => C5 | "4" => C4 | "3" => C3 | _ => C2
    end.
  Definition byte_of_card (c : card) : byte :=
    match c with
    | CA => "A" | CK => "K" | CQ => "Q" | CJ => "J" | CT => "T"
    | C9 => "9" | C8 => "8" | C7 => "7" | C6 => "6"
    | C5 => "5" | C4 => "4" | C3 => "3" | C2 => "2"
    end.

  Definition eqb (a b : card) : bool :=
    Byte.eqb (byte_of_card a) (byte_of_card b).
End Card.

Module Hand.
  Import Card.

  Definition hand_raw : Type := (card * card * card * card * card).
  Inductive hand : Type :=
    HandOf : hand_raw -> (card -> N) -> hand.
  Definition t : Type := hand.

  Declare Scope hand_scope.
  Delimit Scope hand_scope with hand.
  Bind Scope hand_scope with hand.
  Local Open Scope hand_scope.

  Inductive type : Set :=
  | FiveOfAKind | FourOfAKind | FullHouse | ThreeOfAKind | TwoPair | OnePair | HighCard.
  Definition score : Type := type * hand_raw.

  Definition type_to_N (t : type) : N :=
    match t with
    | FiveOfAKind => 6 | FourOfAKind => 5 | FullHouse => 4
    | ThreeOfAKind => 3 | TwoPair => 2 | OnePair => 1 | HighCard => 0
    end.
  Definition type_eqb (l r : type) := N.eqb (type_to_N l) (type_to_N r).

  Definition hand_get (h : hand) : card -> N :=
    let '(HandOf _ hf) := h in hf.

  Definition type_fold_fn : Type := card * N -> type -> type.
  Definition type_fold1 (card_and_count : card * N) (ty : type) : type :=
    let '(c, count) := card_and_count in
    match (ty, count) with
    | (_, 5) => FiveOfAKind
    | (_, 4) => FourOfAKind
    | (ThreeOfAKind, 2) | (OnePair, 3) => FullHouse
    | (_, 3) => ThreeOfAKind
    | (OnePair, 2) => TwoPair
    | (_, 2) => OnePair
    | _ => ty
    end.
  Definition type_fold2 (card_and_count : card * N) (ty : type) : type :=
    let '(c, count) := card_and_count in
    match c with
    | CJ =>
        match (ty, count) with
        | (FourOfAKind, 1) | (ThreeOfAKind, 2) | (OnePair, 3) | (HighCard, 4) => FiveOfAKind
        | (ThreeOfAKind, 1) | (OnePair, 2) | (HighCard, 3) => FourOfAKind
        | (TwoPair, 1) => FullHouse
        | (OnePair, 1) | (HighCard, 2) => ThreeOfAKind
        | (HighCard, 1) => OnePair
        | _ => type_fold1 card_and_count ty
        end
    | _ => type_fold1 card_and_count ty
    end.

  Definition get_score (tf : type_fold_fn) (h : hand) : score :=
    let '(HandOf first_card hf) := h in
    let ty := Card.map (fun c => (c, hf c)) tf HighCard in
    (ty, first_card).

  Fixpoint count_cards (cs : list card) (acc : N) (v : card) : N :=
    match cs with
    | [] => acc
    | c::ctl =>
        let acc' := if Card.eqb c v then N.succ acc else acc in
        count_cards ctl acc' v
    end.
  Definition hand_of_list_byte (bs : list byte) : hand :=
    match List.map Card.card_of_byte bs with
    | (a::b::c::d::e::[]) as cs => HandOf (a, b, c, d, e) (count_cards cs 0)
    | _ => HandOf (C2, C2, C2, C2, C2) (fun _ => 0)
    end.

  Definition hand_of_string (s : string) : hand :=
    hand_of_list_byte (list_byte_of_string s).
End Hand.

Import Card Hand.

Module Type HandOrd.
  Parameter fold_fn : type_fold_fn.
  Parameter card_to_N : card -> N.
End HandOrd.

Module InpTy.
  Definition t : Type := string * N.
End InpTy.

Module MakeHandSort (H : HandOrd).
  Module Map.
    Definition map (h : InpTy.t) : N * (N * N * N * N * N) :=
      let '(ty, (a, b, c, d, e)) :=
        Hand.get_score
          H.fold_fn
          (hand_of_string (fst h)) in
      (type_to_N ty,
        (H.card_to_N a,
          H.card_to_N b,
          H.card_to_N c,
          H.card_to_N d,
          H.card_to_N e)).
  End Map.
  Module PO_N_N := PairOrderedType N N.
  Module PO_N_N_N := PairOrderedType PO_N_N N.
  Module PO_N_N_N_N := PairOrderedType PO_N_N_N N.
  Module PO_N_N_N_N_N := PairOrderedType PO_N_N_N_N N.
  Module OrderedTuple := PairOrderedType N PO_N_N_N_N_N.
  Module OrderedTuple_Alt := OT_to_Alt OrderedTuple.
  Module OBF := OrderByFun InpTy OrderedTuple_Alt Map.
  Module HandOrdOT := OT_from_Alt OBF.
  Module HandOrdFull := OT_to_Full HandOrdOT.
  Module Hand_TTLB := OTF_to_TTLB HandOrdFull.
  Module Sorter := Sort Hand_TTLB.
End MakeHandSort.

Module Part1HandOrd.
  Definition fold_fn := type_fold1.
  Definition card_to_N (c : card) : N :=
    match c with    
    | CA => 12 | CK => 11 | CQ => 10 | CJ => 9
    | CT => 8 | C9 => 7 | C8 => 6 | C7 => 5
    | C6 => 4 | C5 => 3 | C4 => 2
    | C3 => 1 | C2 => 0
    end.
End Part1HandOrd.
Module Part2HandOrd.
  Definition fold_fn := type_fold2.
  Definition card_to_N (c : card) : N :=
    match c with
    | CJ => 0
    | _ => N.succ (Part1HandOrd.card_to_N c)
    end.
End Part2HandOrd.

Declare Custom Entry hand.
Notation "'input' hand .. hands" :=
  (cons hand .. (cons hands nil) ..)
    (at level 200, hand custom hand at level 2, only parsing).
Notation "handv bid" :=
  (handv % string, bid)
    (in custom hand at level 2, handv constr at level 1, bid constr at level 1).

Module Part1Sort := MakeHandSort Part1HandOrd.
Module Part2Sort := MakeHandSort Part2HandOrd.

Fixpoint count_bids (acc idx : N) (inp : list InpTy.t) :=
  match inp with
  | [] => acc
  | (_, bid)::itl =>
      let acc' := acc + idx * bid in
      count_bids acc' (N.succ idx) itl
  end.
Definition sum_bids (inp : list InpTy.t) := count_bids 0 1 inp.

Definition compute_scores (inp : list InpTy.t) :=
  List.map (fun '(h, _) =>
              let p1 := fst (get_score Part1HandOrd.fold_fn (hand_of_string h)) in
              let p2 := fst (get_score Part2HandOrd.fold_fn (hand_of_string h)) in
              (h, (type_eqb p1 p2, p1, p2))) inp.

Definition main inp :=
  (sum_bids (Part1Sort.Sorter.sort inp),
    sum_bids (Part2Sort.Sorter.sort inp)).

Definition example := input
"32T3K" 765
"T55J5" 684
"KK677" 28
"KTJJT" 220
"QQQJA" 483
.

Example sample_input: main example = (6440, 5905).
Proof. simpl. reflexivity. Qed.
