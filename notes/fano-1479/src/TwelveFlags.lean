import AndRoot
import FactorSupport

namespace FanoFactor

open PEqualNP.CircuitLowerBounds FanoPadding

def closedNeighborhood (i : Fin 14) := insert i (neighbors i)

def farFlags (i : Fin 14) : Finset (Fin 7 × Fin 7) := Finset.univ.filter fun e =>
  (e.1 = e.2 ∨ e.1 = e.2+1 ∨ e.1 = e.2+3) ∧
  Fin.castAdd 7 e.1 ∉ closedNeighborhood i ∧ Fin.natAdd 7 e.2 ∉ closedNeighborhood i

set_option maxHeartbeats 2000000 in
theorem far_count : ∀ c : Fin 14, (farFlags c).card = 12 := by decide +kernel

theorem centered_support {A B : Input → Bool} (ma : Increasing A) (mb : Increasing B)
    (sound : ∀ x, A x = true → B x = true → incidence x = true)
    (na : (support A).Nonempty) (nb : (support B).Nonempty) :
    ∃ c : Fin 14, support A ∪ support B ⊆ closedNeighborhood c := by
  have one {U V : Input → Bool} (small : (support U).card ≤ 1)
      (nonempty : (support U).Nonempty)
      (cross : ∀ i ∈ support U, ∀ j ∈ support V, j ∈ neighbors i) :
      ∃ c : Fin 14, support U ∪ support V ⊆ closedNeighborhood c := by
    obtain ⟨c,hc⟩ := nonempty
    refine ⟨c,?_⟩
    intro j hj
    rcases Finset.mem_union.mp hj with hu | hv
    · exact Finset.mem_insert.mpr (Or.inl (Finset.card_le_one.mp small j hu c hc))
    · exact Finset.mem_insert.mpr (Or.inr (cross c hc j hv))
  rcases narrow_support ma mb sound with sa | sb
  · exact one sa na (fun _ hi _ hj => supported_neighbor ma mb sound hi hj)
  · obtain ⟨c,inside⟩ := one sb nb (fun _ hi _ hj =>
      supported_neighbor mb ma (fun x hb ha => sound x ha hb) hi hj)
    exact ⟨c,by simpa [Finset.union_comm] using inside⟩

/-- A correct AND-output circuit with singleton witnesses in both operands
    has double rereads on a fixed set of twelve incidences, at every size. -/
theorem twelve_double_flags (C : Circuit) (normal : Normal C) (correct : Spec C)
    {k a b : ℕ} (out : C.output = 14+k) (gate : C.gates[k]? = some ⟨.and,[a,b]⟩)
    (sa : hasSingleton C a) (sb : hasSingleton C b) :
    ∃ S : Finset (Fin 7 × Fin 7), S.card = 12 ∧ ∀ e ∈ S,
      (e.1=e.2 ∨ e.1=e.2+1 ∨ e.1=e.2+3) ∧
      Trace C (Fin.castAdd 7 e.1) (Fin.natAdd 7 e.2) ∧
      Trace C (Fin.natAdd 7 e.2) (Fin.castAdd 7 e.1) := by
  obtain ⟨_,u,v,ins,_,ha,hb⟩ := normal k _ gate
  obtain ⟨rfl,rfl⟩ : a=u ∧ b=v := by simpa using ins
  have good (x : Input) : C.eval (List.ofFn x) = true ↔ incidence x = true := by
    simpa only [incidence,decide_eq_true_eq] using correct x
  obtain ⟨i,hi⟩ := sa
  obtain ⟨j,hj⟩ := sb
  obtain ⟨c,inside⟩ := centered_support (increasing_signal C normal a)
    (increasing_signal C normal b) (sound_and good out gate ha hb)
    ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  have off {t : Fin 14} (far : t ∉ closedNeighborhood c) :
      signal C a (unitAt t) = false ∧ signal C b (unitAt t) = false := by
    constructor
    · exact Bool.eq_false_iff.mpr fun on => far (inside (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,on⟩)))
    · exact Bool.eq_false_iff.mpr fun on => far (inside (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,on⟩)))
  refine ⟨farFlags c,far_count c,?_⟩
  intro e he
  obtain ⟨inc,fp,fl⟩ := (Finset.mem_filter.mp he).2
  exact ⟨inc,trace_of_dark_and C normal _ _ out gate (off fp).1 (off fp).2,
    trace_of_dark_and C normal _ _ out gate (off fl).1 (off fl).2⟩

end FanoFactor

#print axioms FanoFactor.twelve_double_flags
