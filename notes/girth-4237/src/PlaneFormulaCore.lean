import Mathlib.Data.List.Basic

inductive PlaneFormula (α : Type) where
  | leaf (a : α)
  | bot
  | or (l r : PlaneFormula α)
  | and (l r : PlaneFormula α)

namespace PlaneFormula

def eval {α : Type} (v : α → Bool) : PlaneFormula α → Bool
  | .leaf a => v a
  | .bot => false
  | .or l r => eval v l || eval v r
  | .and l r => eval v l && eval v r

def leaves {α : Type} : PlaneFormula α → List α
  | .leaf a => [a]
  | .bot => []
  | .or l r | .and l r => l.leaves ++ r.leaves

end PlaneFormula
