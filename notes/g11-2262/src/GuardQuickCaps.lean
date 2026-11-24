import GuardSingle0
import GuardSingle1
import GuardSingle2
import GuardSingle3
import GuardSingle4
import GuardSingle5
import GuardSingle6
import GuardSingle7
import GuardSingle8
import GuardSingle9
import GuardSingle10
import GuardSingle11
import GuardSingle12
import GuardSingle13
import GuardSingle14
import GuardSingle15
import GuardSingle16
import GuardSingle17

namespace G11GuardFront
private theorem block_correct (b : Fin 18) (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (32*b.val+i.val))) = true := by
  fin_cases b
  · exact quick_group_0 i
  · exact quick_group_1 i
  · exact quick_group_2 i
  · exact quick_group_3 i
  · exact quick_group_4 i
  · exact quick_group_5 i
  · exact quick_group_6 i
  · exact quick_group_7 i
  · exact quick_group_8 i
  · exact quick_group_9 i
  · exact quick_group_10 i
  · exact quick_group_11 i
  · exact quick_group_12 i
  · exact quick_group_13 i
  · exact quick_group_14 i
  · exact quick_group_15 i
  · exact quick_group_16 i
  · exact quick_group_17 i
theorem fast_caps (i j : Fin 574) : capOK (major i) (major j) = true := by
  apply row_sound _ j
  let b : Fin 18 := ⟨i.val/32, by have := i.isLt; omega⟩
  let d : Fin 32 := ⟨i.val%32, Nat.mod_lt _ (by decide)⟩
  have eq : Fin.ofNat 574 (32*b.val + d.val) = i := by
    apply Fin.ext
    change (32*(i.val/32) + i.val%32) % 574 = i.val
    rw [Nat.div_add_mod,Nat.mod_eq_of_lt i.isLt]
  exact eq ▸ block_correct b d
end G11GuardFront
