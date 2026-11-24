import TwoRoundHints0
import TwoRoundHints1
import TwoRoundHints2
import TwoRoundHints3
import TwoRoundHints4
import TwoRoundHints5

namespace G11TwoRounds

set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000 in
theorem hints_valid (k : Fin 83) : validHint (hint k) := by
  fin_cases k
  · exact hint_0
  · exact hint_1
  · exact hint_2
  · exact hint_3
  · exact hint_4
  · exact hint_5
  · exact hint_6
  · exact hint_7
  · exact hint_8
  · exact hint_9
  · exact hint_10
  · exact hint_11
  · exact hint_12
  · exact hint_13
  · exact hint_14
  · exact hint_15
  · exact hint_16
  · exact hint_17
  · exact hint_18
  · exact hint_19
  · exact hint_20
  · exact hint_21
  · exact hint_22
  · exact hint_23
  · exact hint_24
  · exact hint_25
  · exact hint_26
  · exact hint_27
  · exact hint_28
  · exact hint_29
  · exact hint_30
  · exact hint_31
  · exact hint_32
  · exact hint_33
  · exact hint_34
  · exact hint_35
  · exact hint_36
  · exact hint_37
  · exact hint_38
  · exact hint_39
  · exact hint_40
  · exact hint_41
  · exact hint_42
  · exact hint_43
  · exact hint_44
  · exact hint_45
  · exact hint_46
  · exact hint_47
  · exact hint_48
  · exact hint_49
  · exact hint_50
  · exact hint_51
  · exact hint_52
  · exact hint_53
  · exact hint_54
  · exact hint_55
  · exact hint_56
  · exact hint_57
  · exact hint_58
  · exact hint_59
  · exact hint_60
  · exact hint_61
  · exact hint_62
  · exact hint_63
  · exact hint_64
  · exact hint_65
  · exact hint_66
  · exact hint_67
  · exact hint_68
  · exact hint_69
  · exact hint_70
  · exact hint_71
  · exact hint_72
  · exact hint_73
  · exact hint_74
  · exact hint_75
  · exact hint_76
  · exact hint_77
  · exact hint_78
  · exact hint_79
  · exact hint_80
  · exact hint_81
  · exact hint_82

end G11TwoRounds
