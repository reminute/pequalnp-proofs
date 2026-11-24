import PartnerCertificate
import RejectWitness

namespace Cubic1971.PartnerWidth

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open StarReader PartnerCertificate

/-- After a sole AND reader with a positive suffix, no choice of two other raw
    coordinates determines the partner, even if either coordinate is marked. -/
theorem no_pair {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (v : Fin n) (ordinary : ∀ {u w}, G.Adj u w → u ∉ A)
    (girth : GirthEdgeNegatives.GirthFive G) (degree : (G.neighborSet v).ncard = 3)
    (hv : v ∉ A) (C : Circuit) (pre post : List Gate) (r : Gate) (k : Nat)
    (layout : C.gates = pre ++ r :: post) (legal : FanInTwo C)
    (sole : ∀ g ∈ pre ++ post, ¬effective v.val g) (op : r.op = .and)
    (args : r.inputs = [v.val,k] ∨ r.inputs = [k,v.val]) (other : k ≠ v.val)
    (output : C.output ≠ v.val) (correct : circuitFun n C = graphFun G A)
    (least : ∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s)
    (pos : ∀ g ∈ post, g.op ≠ .not)
    (K : Finset (Fin n)) (small : K.card ≤ 2) (notCenter : v ∉ K) :
    ∃ x y : Fin n → Bool, (∀ u ∈ K, x u = y u) ∧
      (run pre (List.ofFn x)).getD k false ≠ (run pre (List.ofFn y)).getD k false := by
  classical
  by_contra! support
  have enabled := circuit_enabled C pre post r k true layout legal sole op args other output correct hv
  obtain ⟨x,off,_,low⟩ := RejectWitness.and_witness n C v pre post r k layout legal least op args pos
  have graphOff : graphFun G A x = false := correct ▸ off
  let S := Finset.univ.filter (fun u => u ≠ v ∧ x u = true)
  have smem (u : Fin n) : u ∈ S ↔ u ≠ v ∧ x u = true := by simp [S]
  have away : v ∉ S := by simp [S]
  have reject : ¬((∃ a ∈ A, x a = true) ∨ ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true) := by
    intro yes
    have on : graphFun G A x = true := by
      simpa only [graphFun,Bool.or_eq_true,decide_eq_true_eq] using yes
    exact Bool.noConfusion (graphOff.symm.trans on)
  have good : clean A S := fun u us ua => reject (Or.inl ⟨u,ua,((smem u).mp us).2⟩)
  have ind : free G S := fun u us w ws adj =>
    reject (Or.inr ⟨u,w,adj,((smem u).mp us).2,((smem w).mp ws).2⟩)
  have pass := supported_pair (physical pre k) true enabled @ordinary girth degree K small
      (fun U V _ _ h => support (bits U) (bits V)
        (fun u uk => by simp only [bits,decide_eq_decide]; exact h u uk)) S away good ind
  have matchRow : (run pre (List.ofFn x)).getD k false = physical pre k S := by
    apply support
    intro u uk
    have ne : u ≠ v := fun h => notCenter (h ▸ uk)
    simp [bits,smem,ne]
  change (run pre (List.ofFn x)).getD k false = false at low
  exact Bool.noConfusion (low.symm.trans (matchRow.trans pass))

end Cubic1971.PartnerWidth

#print axioms Cubic1971.PartnerWidth.no_pair
