import GuardPacked

namespace G11GuardFront

def guarded (neg : Nat) : Nat :=
  (List.range 11).foldl (fun m v => if neg &&& vertexNeg[v]! = 0 then m ||| stars[v]! else m) 0

def profile (i j : Fin 64) : Profile :=
  let pos := positives[i.val]! &&& positives[j.val]!
  let neg := negatives[i.val]! &&& negatives[j.val]!
  ⟨pos, neg, pos &&& guarded neg, permitted[i.val]! &&& permitted[j.val]!⟩

def admissible (i j : Fin 64) : Bool :=
  let a := vertices[i.val]!
  let b := vertices[j.val]!
  let neg := negatives[i.val]! &&& negatives[j.val]!
  neg != 0 && a &&& b != a && a &&& b != b

def subBits (a b : Nat) : Bool := a &&& b == a

def dominates (a b : Profile) : Bool :=
  subBits a.pos b.pos && subBits b.neg a.neg && subBits a.guard b.guard && subBits a.kept b.kept

def majorIndex (i j : Fin 64) : Fin 574 := packedIndex i j
def major (i : Fin 574) : Profile := packedMajor i

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem majorizes : ∀ i j : Fin 64, admissible i j = true →
    dominates (profile i j) (major (majorIndex i j)) = true := by decide

def upper (a b : Profile) : Nat :=
  (a.pos &&& b.pos ||| a.guard ||| b.guard) &&& a.kept &&& b.kept

def capOK (a b : Profile) : Bool :=
  if a.neg &&& b.neg != 0 then true else
    let m := upper a b
    m == 18453 || m.bitIndices.length ≤ 4

end G11GuardFront
