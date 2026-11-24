import FlagOrbits

namespace FanoFlag

inductive PairKind where
  | sameShore
  | incidentCross
  | nonincidentCross
  deriving DecidableEq

def kind (a b : V) : PairKind :=
  if (a.val<7 ↔ b.val<7) then .sameShore
  else if adj a b then .incidentCross else .nonincidentCross

def representativesOf (k : PairKind) : List R := (List.finRange 14).filter fun i =>
  decide (kind (rep i).1 (rep i).2=k)

theorem grouped_representatives :
    representativesOf .sameShore=[0,1,5,6,10,11] ∧
    representativesOf .incidentCross=[2,4,7,12] ∧
    representativesOf .nonincidentCross=[3,8,9,13] := by decide +kernel

theorem grouped_sizes :
    pairs.countP (fun p => decide (kind p.1 p.2=.sameShore))=42 ∧
    pairs.countP (fun p => decide (kind p.1 p.2=.incidentCross))=21 ∧
    pairs.countP (fun p => decide (kind p.1 p.2=.nonincidentCross))=28 := by decide +kernel

theorem keeps_kind : ∀ (g : G) (a b : V), kind (perm g a) (perm g b)=kind a b := by decide +kernel

end FanoFlag
