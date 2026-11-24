import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_160 : quickRow ⟨772,461482,768,23807⟩ = true := by decide
theorem row_cert_161 : quickRow ⟨772,461562,768,56567⟩ = true := by decide
theorem row_cert_162 : quickRow ⟨772,469690,512,56799⟩ = true := by decide
theorem row_cert_163 : quickRow ⟨772,494250,768,31967⟩ = true := by decide
theorem row_cert_164 : quickRow ⟨772,494523,768,64727⟩ = true := by decide
theorem row_cert_165 : quickRow ⟨772,1904366,256,64247⟩ = true := by decide
theorem row_cert_166 : quickRow ⟨772,8882858,256,32503⟩ = true := by decide
theorem row_cert_167 : quickRow ⟨773,330410,772,31997⟩ = true := by decide
theorem row_cert_168 : quickRow ⟨774,30037,774,64761⟩ = true := by decide
theorem row_cert_169 : quickRow ⟨775,491519,514,56797⟩ = true := by decide
theorem row_cert_170 : quickRow ⟨776,9961472,776,64759⟩ = true := by decide
theorem row_cert_171 : quickRow ⟨780,330410,780,65267⟩ = true := by decide
theorem row_cert_172 : quickRow ⟨780,10126677,780,64755⟩ = true := by decide
theorem row_cert_173 : quickRow ⟨788,330410,772,63711⟩ = true := by decide
theorem row_cert_174 : quickRow ⟨789,495342,768,30941⟩ = true := by decide
theorem row_cert_175 : quickRow ⟨800,28672,800,64735⟩ = true := by decide
theorem row_cert_176 : quickRow ⟨802,28672,802,64733⟩ = true := by decide
theorem row_cert_177 : quickRow ⟨804,192785,804,64731⟩ = true := by decide
theorem row_cert_178 : quickRow ⟨806,193877,806,64729⟩ = true := by decide
theorem row_cert_179 : quickRow ⟨820,523259,544,56797⟩ = true := by decide
theorem row_cert_180 : quickRow ⟨1024,2184,1024,65523⟩ = true := by decide
theorem row_cert_181 : quickRow ⟨1024,3276,1024,32766⟩ = true := by decide
theorem row_cert_182 : quickRow ⟨1024,28672,1024,63486⟩ = true := by decide
theorem row_cert_183 : quickRow ⟨1024,1051648,1024,16383⟩ = true := by decide
theorem row_cert_184 : quickRow ⟨1024,1572864,1024,64767⟩ = true := by decide
theorem row_cert_185 : quickRow ⟨1024,1573956,1024,65275⟩ = true := by decide
theorem row_cert_186 : quickRow ⟨1024,4210688,1024,47103⟩ = true := by decide
theorem row_cert_187 : quickRow ⟨1024,6291456,1024,65487⟩ = true := by decide
theorem row_cert_188 : quickRow ⟨1026,1601536,0,62718⟩ = true := by decide
theorem row_cert_189 : quickRow ⟨1026,6294732,0,32718⟩ = true := by decide
theorem row_cert_190 : quickRow ⟨1027,32767,3,30718⟩ = true := by decide
theorem row_cert_191 : quickRow ⟨1036,2184,1036,64499⟩ = true := by decide
theorem quick_group_5 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (160+i.val))) = true := by
  fin_cases i
  · exact row_cert_160
  · exact row_cert_161
  · exact row_cert_162
  · exact row_cert_163
  · exact row_cert_164
  · exact row_cert_165
  · exact row_cert_166
  · exact row_cert_167
  · exact row_cert_168
  · exact row_cert_169
  · exact row_cert_170
  · exact row_cert_171
  · exact row_cert_172
  · exact row_cert_173
  · exact row_cert_174
  · exact row_cert_175
  · exact row_cert_176
  · exact row_cert_177
  · exact row_cert_178
  · exact row_cert_179
  · exact row_cert_180
  · exact row_cert_181
  · exact row_cert_182
  · exact row_cert_183
  · exact row_cert_184
  · exact row_cert_185
  · exact row_cert_186
  · exact row_cert_187
  · exact row_cert_188
  · exact row_cert_189
  · exact row_cert_190
  · exact row_cert_191
end G11GuardFront
