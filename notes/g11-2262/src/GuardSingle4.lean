import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_128 : quickRow ⟨257,356352,0,61949⟩ = true := by decide
theorem row_cert_129 : quickRow ⟨259,32767,3,32252⟩ = true := by decide
theorem row_cert_130 : quickRow ⟨268,10126677,268,65267⟩ = true := by decide
theorem row_cert_131 : quickRow ⟨272,30856,0,30175⟩ = true := by decide
theorem row_cert_132 : quickRow ⟨275,32767,3,30172⟩ = true := by decide
theorem row_cert_133 : quickRow ⟨304,521011,48,63951⟩ = true := by decide
theorem row_cert_134 : quickRow ⟨305,521011,48,61901⟩ = true := by decide
theorem row_cert_135 : quickRow ⟨512,2184,512,65487⟩ = true := by decide
theorem row_cert_136 : quickRow ⟨512,2560,512,53247⟩ = true := by decide
theorem row_cert_137 : quickRow ⟨512,65546,512,57279⟩ = true := by decide
theorem row_cert_138 : quickRow ⟨512,327680,512,65532⟩ = true := by decide
theorem row_cert_139 : quickRow ⟨512,1572864,512,64255⟩ = true := by decide
theorem row_cert_140 : quickRow ⟨512,6291456,512,65523⟩ = true := by decide
theorem row_cert_141 : quickRow ⟨512,8388608,512,32511⟩ = true := by decide
theorem row_cert_142 : quickRow ⟨512,9961472,512,65271⟩ = true := by decide
theorem row_cert_143 : quickRow ⟨515,327680,515,65020⟩ = true := by decide
theorem row_cert_144 : quickRow ⟨518,1365,518,65017⟩ = true := by decide
theorem row_cert_145 : quickRow ⟨524,6291456,524,65011⟩ = true := by decide
theorem row_cert_146 : quickRow ⟨547,491520,547,64988⟩ = true := by decide
theorem row_cert_147 : quickRow ⟨548,164113,548,64987⟩ = true := by decide
theorem row_cert_148 : quickRow ⟨550,165205,550,64985⟩ = true := by decide
theorem row_cert_149 : quickRow ⟨560,2184,560,64975⟩ = true := by decide
theorem row_cert_150 : quickRow ⟨562,3276,562,64973⟩ = true := by decide
theorem row_cert_151 : quickRow ⟨770,28672,770,64765⟩ = true := by decide
theorem row_cert_152 : quickRow ⟨772,330474,768,55551⟩ = true := by decide
theorem row_cert_153 : quickRow ⟨772,331502,768,63741⟩ = true := by decide
theorem row_cert_154 : quickRow ⟨772,331775,768,64757⟩ = true := by decide
theorem row_cert_155 : quickRow ⟨772,338602,516,56819⟩ = true := by decide
theorem row_cert_156 : quickRow ⟨772,338682,512,56829⟩ = true := by decide
theorem row_cert_157 : quickRow ⟨772,359082,516,64979⟩ = true := by decide
theorem row_cert_158 : quickRow ⟨772,359082,516,65009⟩ = true := by decide
theorem row_cert_159 : quickRow ⟨772,359355,512,64989⟩ = true := by decide
theorem quick_group_4 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (128+i.val))) = true := by
  fin_cases i
  · exact row_cert_128
  · exact row_cert_129
  · exact row_cert_130
  · exact row_cert_131
  · exact row_cert_132
  · exact row_cert_133
  · exact row_cert_134
  · exact row_cert_135
  · exact row_cert_136
  · exact row_cert_137
  · exact row_cert_138
  · exact row_cert_139
  · exact row_cert_140
  · exact row_cert_141
  · exact row_cert_142
  · exact row_cert_143
  · exact row_cert_144
  · exact row_cert_145
  · exact row_cert_146
  · exact row_cert_147
  · exact row_cert_148
  · exact row_cert_149
  · exact row_cert_150
  · exact row_cert_151
  · exact row_cert_152
  · exact row_cert_153
  · exact row_cert_154
  · exact row_cert_155
  · exact row_cert_156
  · exact row_cert_157
  · exact row_cert_158
  · exact row_cert_159
end G11GuardFront
