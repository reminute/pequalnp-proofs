import GuardClauseBase

namespace G11GuardFront
open G11Certificate G11Protected
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

theorem pos_correct : ∀ (i : Fin 64) (e : Fin 16),
    positives[i.val]!.testBit e.val = true ↔ ¬ Disjoint (edge e) (support i) := by decide

theorem neg_correct : ∀ (i : Fin 64) (z : Fin 24),
    negatives[i.val]!.testBit z.val = true ↔ ¬ Disjoint (negative z) (support i) := by decide


end G11GuardFront
