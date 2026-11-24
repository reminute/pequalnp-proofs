import GuardHosts

namespace G11GuardFront
open G11Certificate G11Protected
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

theorem singleton_rep : ∀ c : Fin 11,
    ∃ i : Fin 64, support i = {c} ∧ ∀ e : Fin 16, permitted[i.val]!.testBit e.val = true := by decide

private theorem covers_host (c : Fin 11) :
    ((neighbors ∅ c).powerset.erase ∅) ⊆ (hosts c).image support := by
  fin_cases c <;> decide

private theorem host_kept (c : Fin 11) : ∀ i ∈ hosts c, ∀ e : Fin 16,
    permitted[i.val]!.testBit e.val = false → incidentTo e c (support i) := by
  fin_cases c <;> decide

theorem neighborhood_rep (c : Fin 11) (A : Finset (Fin 11)) (mem : A ∈ (neighbors ∅ c).powerset)
    (ne : A.Nonempty) : ∃ i : Fin 64, support i = A ∧
      ∀ e : Fin 16, permitted[i.val]!.testBit e.val = false → incidentTo e c A := by
  obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp (covers_host c (Finset.mem_erase.mpr ⟨ne.ne_empty,mem⟩))
  exact ⟨i,eq,eq ▸ host_kept c i hi⟩

theorem edge_unique : ∀ i j : Fin 16,
    ((edgeAt i = edgeAt j) ∨ (edgeAt i = (edgeAt j).swap)) → i = j := by decide

theorem no_deleted_neighbor (U : Finset (Fin 16)) (e : Fin 16) (he : e ∈ U) :
    (edgeAt e).2 ∉ neighbors U (edgeAt e).1 ∧ (edgeAt e).1 ∉ neighbors U (edgeAt e).2 := by
  constructor <;> intro h <;> obtain ⟨k,hk,ab|ba⟩ := (Finset.mem_filter.mp h).2
  · exact hk (edge_unique k e (Or.inl (Prod.ext ab.1 ab.2)) ▸ he)
  · exact hk (edge_unique k e (Or.inr (Prod.ext ba.1 ba.2)) ▸ he)
  · exact hk (edge_unique k e (Or.inr (Prod.ext ab.1 ab.2)) ▸ he)
  · exact hk (edge_unique k e (Or.inl (Prod.ext ba.1 ba.2)) ▸ he)

theorem clause_rep {U : Finset (Fin 16)} {A : Finset (Fin 11)} (ha : allowed U A)
    (ne : A.Nonempty) : ∃ i : Fin 64, support i = A ∧
    ∀ e ∈ U, permitted[i.val]!.testBit e.val = true := by
  rcases ha with ⟨c, sc⟩ | ⟨c, sc⟩
  · have same : A = {c} := by
      obtain ⟨v,hv⟩ := ne
      have eqv := Finset.mem_singleton.mp (sc hv)
      exact Finset.Subset.antisymm sc (Finset.singleton_subset_iff.mpr (eqv ▸ hv))
    obtain ⟨i,hi,all⟩ := singleton_rep c
    exact ⟨i,hi.trans same.symm,fun e _ => all e⟩
  · have incl := sc.trans (neighbors_anti (Finset.empty_subset U) c)
    obtain ⟨i,hi,miss⟩ := neighborhood_rep c A (Finset.mem_powerset.mpr incl) ne
    refine ⟨i,hi,?_⟩
    intro e he
    cases h : permitted[i.val]!.testBit e.val with
    | true => rfl
    | false =>
      rcases miss e h with ⟨left,hv⟩ | ⟨right,hv⟩
      · exact False.elim ((no_deleted_neighbor U e he).1 (left.symm ▸ sc hv))
      · exact False.elim ((no_deleted_neighbor U e he).2 (right.symm ▸ sc hv))


end G11GuardFront
