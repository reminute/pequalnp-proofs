import ErasePartner
import L_meta_2305
import L_meta_2307

/- The checked constant propagator is the one in L-meta-2305, adapted there from
   stierms's L-meta-517. L-meta-2307 supplies the eight-input lower bound. -/
namespace Petersen3831.Cofactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2305 RawPartner

/-- Pin physical input zero, keeping the eight remaining input numbers in order. -/
def start (b : Bool) : List Stat × List Gate :=
  (Sum.inl b :: List.ofFn (fun i : Fin 8 => (Sum.inr i.val : Stat)), [])

def compiled (C : Circuit) (b : Bool) : List Stat × List Gate :=
  elim 8 (C.gates.map normGate) (start b)

private theorem initial_valid (y : Fin 8 → Bool) (b : Bool) :
    Inv 8 (List.ofFn y) (b :: List.ofFn y) (start b) := by
  refine ⟨by simp [start], ?_⟩
  intro i
  by_cases hi : i < 9
  · interval_cases i <;> simp [start, List.ofFn_succ, wiresFrom, Stat.Valid, Stat.val]
  · rw [List.getD_eq_default _ _ (by simp [start]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem correct (C : Circuit) (fan : FanInTwo C) (b : Bool) (y : Fin 8 → Bool) :
    ((compiled C b).1.getD C.output (Sum.inl false)).val
      (wiresFrom (compiled C b).2 (List.ofFn y)) = circuitFun 9 C (Fin.cons b y) := by
  have valid : ∀ g ∈ C.gates.map normGate, Ok g := by
    intro g hg
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    exact (normGate_nok h (fan h hh)).1
  have inv := inv_elim 8 (List.ofFn y) (by simp) (C.gates.map normGate)
    (b :: List.ofFn y) (start b) valid (initial_valid y b)
  have h := (inv.2 C.output).2
  rw [wiresFrom_norm] at h
  have hof : List.ofFn (Fin.cons b y : Input) = b :: List.ofFn y := by
    simp [List.ofFn_succ]
  unfold circuitFun Circuit.eval
  rw [hof, wires_eq]
  exact h

def residual (y : Fin 8 → Bool) := graph (Fin.cons false y)

private theorem pin (y : Fin 8 → Bool) : flip (Fin.cons false y) = Fin.cons true y := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [RawPartner.flip]

theorem survivors (C : Circuit) (fan : FanInTwo C)
    (spec : ∀ x : Input, circuitFun 9 C (flip x) = graph x) :
    ∃ j, (compiled C true).1.getD C.output (Sum.inl false) = Sum.inr j ∧
      let D : Circuit := ⟨(compiled C true).2, j⟩
      FanInTwo D ∧ (∀ y, circuitFun 8 D y = residual y) ∧ 12 ≤ D.size := by
  have bound : ¬ HasCircuitSize 8 residual 11 := PEqualNP.Outside.L_meta_2307
  have value (y : Fin 8 → Bool) := (correct C fan true y).trans
    ((congrArg (circuitFun 9 C) (pin y).symm).trans (spec (Fin.cons false y)))
  cases status : (compiled C true).1.getD C.output (Sum.inl false) with
  | inl c =>
    have h0 := value (fun _ => false)
    have h1 := value (fun _ => true)
    rw [status] at h0 h1
    have hl : c = false := h0
    have hr : c = true := h1
    simp_all
  | inr j =>
    let D : Circuit := ⟨(compiled C true).2, j⟩
    have hfan : FanInTwo D := elim_ok 8 _ (start true) (by simp [start])
    have heval (y) : circuitFun 8 D y = residual y := by
      have h := value y
      rw [status] at h
      exact h
    refine ⟨j, rfl, hfan, heval, ?_⟩
    by_contra! few
    change D.size < 12 at few
    exact bound ⟨D, hfan, by omega, heval⟩

theorem size_window (C : Circuit) (fan : FanInTwo C)
    (spec : ∀ x : Input, circuitFun 9 C (flip x) = graph x) :
    12 ≤ (compiled C true).2.length ∧ (compiled C true).2.length ≤ C.size := by
  obtain ⟨_, _, _, _, h⟩ := survivors C fan spec
  exact ⟨h, by simpa [compiled,start,Circuit.size] using
    (elim_len 8 (C.gates.map normGate) (start true))⟩

end Petersen3831.Cofactor
