import GuardExplicit
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

namespace G11GuardFront

def encodeCaps : List Nat → Nat
  | [] => 0
  | m :: xs => 2^m ||| encodeCaps xs

private theorem encode_spec (xs : List Nat) (n : Nat) :
    (encodeCaps xs).testBit n = true ↔ n ∈ xs := by
  induction xs with
  | nil => simp [encodeCaps]
  | cons m xs ih =>
    simp only [encodeCaps, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

set_option exponentiation.threshold 65536 in
private theorem encoding : capBits = encodeCaps capValues := by decide
private theorem values_good : capValues.all (fun m => m == 18453 || m.bitIndices.length ≤ 4) = true := by decide
private theorem rows_eq : (List.finRange 574).map major = explicitRows := by decide

def quick (a b : Profile) : Bool :=
  a.neg &&& b.neg != 0 || capBits.testBit (upper a b)

def quickRow (a : Profile) := explicitRows.all (quick a)

theorem quick_sound (a b : Profile) (h : quick a b = true) : capOK a b = true := by
  by_cases nz : a.neg &&& b.neg != 0
  · simp [capOK,nz]
  · have bit : capBits.testBit (upper a b) = true := by simpa [quick,nz] using h
    rw [encoding] at bit
    have ok := List.all_eq_true.mp values_good _ ((encode_spec _ _).mp bit)
    simpa [capOK,nz] using ok

theorem row_sound {a : Profile} (h : quickRow a = true) (j : Fin 574) :
    capOK a (major j) = true := by
  apply quick_sound
  have member : major j ∈ explicitRows := by
    rw [← rows_eq]
    exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
  exact List.all_eq_true.mp h _ member

end G11GuardFront
