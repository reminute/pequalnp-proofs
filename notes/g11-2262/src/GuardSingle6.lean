import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_192 : quickRow ⟨1048,164113,1048,64487⟩ = true := by decide
theorem row_cert_193 : quickRow ⟨1072,6291456,1072,64463⟩ = true := by decide
theorem row_cert_194 : quickRow ⟨1284,1573956,1284,64251⟩ = true := by decide
theorem row_cert_195 : quickRow ⟨1292,10126677,1292,64243⟩ = true := by decide
theorem row_cert_196 : quickRow ⟨1296,328226,1296,64239⟩ = true := by decide
theorem row_cert_197 : quickRow ⟨1304,492339,1304,64231⟩ = true := by decide
theorem row_cert_198 : quickRow ⟨1536,6293640,0,65475⟩ = true := by decide
theorem row_cert_199 : quickRow ⟨1792,1572864,1792,63743⟩ = true := by decide
theorem row_cert_200 : quickRow ⟨1796,1573956,1796,63739⟩ = true := by decide
theorem row_cert_201 : quickRow ⟨1800,9961472,1800,63735⟩ = true := by decide
theorem row_cert_202 : quickRow ⟨1804,330410,1804,64243⟩ = true := by decide
theorem row_cert_203 : quickRow ⟨1804,10126677,1804,63731⟩ = true := by decide
theorem row_cert_204 : quickRow ⟨2048,192,2048,45055⟩ = true := by decide
theorem row_cert_205 : quickRow ⟨2048,2184,2048,32511⟩ = true := by decide
theorem row_cert_206 : quickRow ⟨2048,327680,2048,64255⟩ = true := by decide
theorem row_cert_207 : quickRow ⟨2048,524300,2048,49023⟩ = true := by decide
theorem row_cert_208 : quickRow ⟨2048,1572864,2048,65532⟩ = true := by decide
theorem row_cert_209 : quickRow ⟨2048,1573956,2048,32759⟩ = true := by decide
theorem row_cert_210 : quickRow ⟨2048,8388608,2048,65487⟩ = true := by decide
theorem row_cert_211 : quickRow ⟨2048,8552448,2048,64503⟩ = true := by decide
theorem row_cert_212 : quickRow ⟨2051,1572864,2051,63484⟩ = true := by decide
theorem row_cert_213 : quickRow ⟨2052,1901636,0,31479⟩ = true := by decide
theorem row_cert_214 : quickRow ⟨2052,8554632,0,31479⟩ = true := by decide
theorem row_cert_215 : quickRow ⟨2060,10126677,12,31735⟩ = true := by decide
theorem row_cert_216 : quickRow ⟨2065,29491,2065,63470⟩ = true := by decide
theorem row_cert_217 : quickRow ⟨2096,8388608,2096,63439⟩ = true := by decide
theorem row_cert_218 : quickRow ⟨2560,1900544,0,64252⟩ = true := by decide
theorem row_cert_219 : quickRow ⟨2560,8390792,0,32463⟩ = true := by decide
theorem row_cert_220 : quickRow ⟨2820,330410,772,31487⟩ = true := by decide
theorem row_cert_221 : quickRow ⟨2828,10457087,264,31479⟩ = true := by decide
theorem row_cert_222 : quickRow ⟨3073,28672,3073,62462⟩ = true := by decide
theorem row_cert_223 : quickRow ⟨3080,8552448,3080,62455⟩ = true := by decide
theorem quick_group_6 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (192+i.val))) = true := by
  fin_cases i
  · exact row_cert_192
  · exact row_cert_193
  · exact row_cert_194
  · exact row_cert_195
  · exact row_cert_196
  · exact row_cert_197
  · exact row_cert_198
  · exact row_cert_199
  · exact row_cert_200
  · exact row_cert_201
  · exact row_cert_202
  · exact row_cert_203
  · exact row_cert_204
  · exact row_cert_205
  · exact row_cert_206
  · exact row_cert_207
  · exact row_cert_208
  · exact row_cert_209
  · exact row_cert_210
  · exact row_cert_211
  · exact row_cert_212
  · exact row_cert_213
  · exact row_cert_214
  · exact row_cert_215
  · exact row_cert_216
  · exact row_cert_217
  · exact row_cert_218
  · exact row_cert_219
  · exact row_cert_220
  · exact row_cert_221
  · exact row_cert_222
  · exact row_cert_223
end G11GuardFront
