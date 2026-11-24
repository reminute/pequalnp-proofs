import RareFree

namespace G11Structure

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem other_witness (ao : IsAO2 n C) (tf : TopForm G C) {j k : ℕ}
    (marked : junk G C = {j,k})
    (source : ∀ u v : Fin n, s(u,v) ∈ Ustar G C → ∃ z ∈ tops G C, ∃ b : Fin 2, ∃ i : ℕ,
      (i = j ∨ i = k) ∧ gateVal n C z (pairInput u v) = true ∧
      OrReaches n C (opnd C z b) i ∧ gateVal n C i (pairInput u v) = true)
    (u v : Fin n) (edge : s(u,v) ∈ Ustar G C) :
    (gateVal n C j (pairInput u v) = true ∧ gateVal n C k (pairInput u v) = true) ∨
    ∃ i ∈ junk G C, gateVal n C i (pairInput u v) = true ∧ (u ∈ wmax G C i ∨ v ∈ wmax G C i) := by
  classical
  obtain ⟨z,zt,b,i,which,onZ,reach,onI⟩ := source u v edge
  have iMem : i ∈ junk G C := by simpa only [marked,Finset.mem_insert,Finset.mem_singleton] using which
  have ht := zt
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at ht
  have onOther := (and_sides ao ht.1 ht.2.1 (pairInput u v)).mp onZ (1-b)
  rcases (operand_iff ao tf ht.1 ht.2.1 (1-b) (pairInput u v)).mp onOther with raw | extra
  · obtain ⟨vertex,rv,hv⟩ := raw
    have endpoint : vertex = u ∨ vertex = v := by simpa [pairInput] using hv
    have safe := same_side_vertex ao zt b reach vertex rv
    exact Or.inr ⟨i,iMem,onI,endpoint.elim (fun eq => Or.inl (eq ▸ safe)) (fun eq => Or.inr (eq ▸ safe))⟩
  · obtain ⟨a,am,ar,hit⟩ := extra
    have diff : i ≠ a := by
      rintro rfl
      apply no_dirty_both_sides ao zt iMem
      fin_cases b
      · exact ⟨reach,ar⟩
      · exact ⟨ar,reach⟩
    rw [marked] at am
    simp only [Finset.mem_insert,Finset.mem_singleton] at am
    rcases which with rfl | rfl <;> rcases am with rfl | rfl <;> first
      | exact (diff rfl).elim
      | exact Or.inl ⟨onI,hit⟩
      | exact Or.inl ⟨hit,onI⟩

end G11Structure
