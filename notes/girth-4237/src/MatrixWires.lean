import RankWires
import RankGates

namespace GirthWires

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

variable {X I J : Type} [Fintype I] [Fintype J]

theorem matrix_sums (M : Matrix I J ℝ) (pos : I → X) (neg : J → X) :
    Sums (GirthPotential.weight M pos neg) :=
  ⟨GirthPotential.const_weight M pos neg,GirthPotential.and_weight M pos neg,
   GirthPotential.or_weight M pos neg⟩

theorem matrix_gate_bound {n : Nat} (M : Matrix I J ℝ) (pos : I → (Fin n → Bool)) (neg : J → (Fin n → Bool))
    {C : Circuit} (mc : Monotone2 C) (j : Fin C.gates.length) :
    GirthPotential.weight M pos neg (gateVal n C j.val) ≤
      ((gateAt C j.val).inputs.map fun w => GirthPotential.weight M pos neg (signal n C w)).sum :=
  gate_bound_total (matrix_sums M pos neg) mc j

end GirthWires
