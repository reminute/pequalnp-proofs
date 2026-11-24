import GuardFrontData
import ProtectedObstruction

namespace G11GuardFront

open G11Certificate G11Protected

def support (i : Fin 64) : Finset (Fin 11) :=
  Finset.univ.filter fun v => vertices[i.val]!.testBit v.val

def incidentTo (e : Fin 16) (c : Fin 11) (A : Finset (Fin 11)) : Prop :=
  ((edgeAt e).1 = c ∧ (edgeAt e).2 ∈ A) ∨ ((edgeAt e).2 = c ∧ (edgeAt e).1 ∈ A)

instance (e : Fin 16) (c : Fin 11) (A : Finset (Fin 11)) : Decidable (incidentTo e c A) := by
  unfold incidentTo; infer_instance

set_option maxRecDepth 30000
set_option maxHeartbeats 10000000


end G11GuardFront
