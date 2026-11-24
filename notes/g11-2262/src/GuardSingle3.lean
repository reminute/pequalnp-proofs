import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_96 : quickRow ⟨48,521011,48,56271⟩ = true := by decide
theorem row_cert_97 : quickRow ⟨48,521011,48,62927⟩ = true := by decide
theorem row_cert_98 : quickRow ⟨48,521011,48,64461⟩ = true := by decide
theorem row_cert_99 : quickRow ⟨48,521139,32,56799⟩ = true := by decide
theorem row_cert_100 : quickRow ⟨48,521203,32,57309⟩ = true := by decide
theorem row_cert_101 : quickRow ⟨48,523195,32,64989⟩ = true := by decide
theorem row_cert_102 : quickRow ⟨49,521011,48,63437⟩ = true := by decide
theorem row_cert_103 : quickRow ⟨50,3276,50,65485⟩ = true := by decide
theorem row_cert_104 : quickRow ⟨51,524287,34,56797⟩ = true := by decide
theorem row_cert_105 : quickRow ⟨64,4111,64,57341⟩ = true := by decide
theorem row_cert_106 : quickRow ⟨64,65546,64,56831⟩ = true := by decide
theorem row_cert_107 : quickRow ⟨64,102403,64,57311⟩ = true := by decide
theorem row_cert_108 : quickRow ⟨64,393216,64,49023⟩ = true := by decide
theorem row_cert_109 : quickRow ⟨64,8486912,64,45055⟩ = true := by decide
theorem row_cert_110 : quickRow ⟨65,397327,0,40829⟩ = true := by decide
theorem row_cert_111 : quickRow ⟨128,4111,128,49150⟩ = true := by decide
theorem row_cert_112 : quickRow ⟨128,524300,128,47103⟩ = true := by decide
theorem row_cert_113 : quickRow ⟨128,2101248,128,16383⟩ = true := by decide
theorem row_cert_114 : quickRow ⟨128,5242880,128,57279⟩ = true := by decide
theorem row_cert_115 : quickRow ⟨128,11010048,128,53247⟩ = true := by decide
theorem row_cert_116 : quickRow ⟨130,5246991,0,40894⟩ = true := by decide
theorem row_cert_117 : quickRow ⟨192,11112463,192,40767⟩ = true := by decide
theorem row_cert_118 : quickRow ⟨192,11505679,128,44927⟩ = true := by decide
theorem row_cert_119 : quickRow ⟨192,16355343,64,53183⟩ = true := by decide
theorem row_cert_120 : quickRow ⟨256,2184,256,30719⟩ = true := by decide
theorem row_cert_121 : quickRow ⟨256,2560,256,16383⟩ = true := by decide
theorem row_cert_122 : quickRow ⟨256,2730,256,32766⟩ = true := by decide
theorem row_cert_123 : quickRow ⟨256,8192,256,56831⟩ = true := by decide
theorem row_cert_124 : quickRow ⟨256,28672,256,64991⟩ = true := by decide
theorem row_cert_125 : quickRow ⟨256,28672,256,65021⟩ = true := by decide
theorem row_cert_126 : quickRow ⟨256,327680,256,62463⟩ = true := by decide
theorem row_cert_127 : quickRow ⟨256,328226,256,64495⟩ = true := by decide
theorem quick_group_3 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (96+i.val))) = true := by
  fin_cases i
  · exact row_cert_96
  · exact row_cert_97
  · exact row_cert_98
  · exact row_cert_99
  · exact row_cert_100
  · exact row_cert_101
  · exact row_cert_102
  · exact row_cert_103
  · exact row_cert_104
  · exact row_cert_105
  · exact row_cert_106
  · exact row_cert_107
  · exact row_cert_108
  · exact row_cert_109
  · exact row_cert_110
  · exact row_cert_111
  · exact row_cert_112
  · exact row_cert_113
  · exact row_cert_114
  · exact row_cert_115
  · exact row_cert_116
  · exact row_cert_117
  · exact row_cert_118
  · exact row_cert_119
  · exact row_cert_120
  · exact row_cert_121
  · exact row_cert_122
  · exact row_cert_123
  · exact row_cert_124
  · exact row_cert_125
  · exact row_cert_126
  · exact row_cert_127
end G11GuardFront
