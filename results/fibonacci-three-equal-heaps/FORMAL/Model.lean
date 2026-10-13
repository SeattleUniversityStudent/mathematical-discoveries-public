import Std
set_option autoImplicit false
namespace RQ9F1
structure Position where
  a : Nat
  b : Nat
  c : Nat
  r : Nat
  deriving DecidableEq, Repr

def moves (s : Position) : List Position :=
  ((List.range (min s.a s.r)).map fun k =>
    { s with a := s.a - (k + 1), r := 2 * (k + 1) }) ++
  ((List.range (min s.b s.r)).map fun k =>
    { s with b := s.b - (k + 1), r := 2 * (k + 1) }) ++
  ((List.range (min s.c s.r)).map fun k =>
    { s with c := s.c - (k + 1), r := 2 * (k + 1) })

-- Finite normal-play strategy derivations. No outcome table is an axiom.
mutual
  inductive Outcome : Position -> Bool -> Prop where
    | win {p q : Position} :
        q ∈ moves p -> Outcome q false -> Outcome p true
    | lose {p : Position} : AllWinning (moves p) -> Outcome p false
  inductive AllWinning : List Position -> Prop where
    | nil : AllWinning []
    | cons {p : Position} {ps : List Position} :
        Outcome p true -> AllWinning ps -> AllWinning (p :: ps)
end
end RQ9F1
