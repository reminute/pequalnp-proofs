import SignalFactor
import OnePad

namespace FanoFactor

open PEqualNP.CircuitLowerBounds FanoPadding

def hasSingleton (C : Circuit) (w : ℕ) := ∃ i : Fin 14, signal C w (unitAt i) = true

/-- The given AND-output circuit already has a doubly reread incidence when
    each of its two operands accepts a singleton. -/
theorem and27 (C : Circuit) (size : C.size ≤ 27) (normal : Normal C) (spec : Spec C)
    {k a b : ℕ} (out : C.output = 14+k) (hg : C.gates[k]? = some ⟨.and,[a,b]⟩)
    (sa : hasSingleton C a) (sb : hasSingleton C b) : Posted := by
  obtain ⟨i,atI⟩ := sa
  obtain ⟨j,atJ⟩ := sb
  obtain ⟨_,u,v,ins,_,ha,hb⟩ := normal k _ hg
  obtain ⟨rfl,rfl⟩ : a=u ∧ b=v := by simpa using ins
  have good (x : Input) : C.eval (List.ofFn x) = true ↔ incidence x = true := by
    simpa only [incidence,decide_eq_true_eq] using spec x
  obtain ⟨t,ua,ub⟩ := dark_factors (increasing_signal C normal a) (increasing_signal C normal b)
    (sound_and good out hg ha hb) atI atJ
  exact finish C size normal spec t t (Or.inl rfl)
    (trace_of_dark_and C normal _ _ out hg ua.1 ub.1)
    (trace_of_dark_and C normal _ _ out hg ua.2 ub.2)

/-- With one free gate, every correct circuit with AND at its output suffices. -/
theorem and26 (C : Circuit) (size : C.size ≤ 26) (normal : Normal C) (spec : Spec C)
    {k a b : ℕ} (out : C.output = 14+k) (hg : C.gates[k]? = some ⟨.and,[a,b]⟩) : Posted := by
  have one (q : ℕ) (operand : q=a ∨ q=b) (none : ¬hasSingleton C q) : Posted := by
    have off (i : Fin 14) : signal C q (unitAt i) = false :=
      Bool.eq_false_iff.mpr (fun on => none ⟨i,on⟩)
    exact FanoOnePad.from_operand C size normal spec out hg operand 0 0 (Or.inl rfl) (off _) (off _)
  by_cases sa : hasSingleton C a
  · by_cases sb : hasSingleton C b
    · exact and27 C (size.trans (by decide)) normal spec out hg sa sb
    · exact one b (Or.inr rfl) sb
  · exact one a (Or.inl rfl) sa

end FanoFactor

#print axioms FanoFactor.and27
#print axioms FanoFactor.and26
