import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_224 : quickRow ⟨3088,1576396,3072,46071⟩ = true := by decide
theorem row_cert_225 : quickRow ⟨3088,1576413,3072,62454⟩ = true := by decide
theorem row_cert_226 : quickRow ⟨3088,1576652,3072,45823⟩ = true := by decide
theorem row_cert_227 : quickRow ⟨3088,1576686,3072,62206⟩ = true := by decide
theorem row_cert_228 : quickRow ⟨3088,1593292,2048,47102⟩ = true := by decide
theorem row_cert_229 : quickRow ⟨3088,1604812,2048,30718⟩ = true := by decide
theorem row_cert_230 : quickRow ⟨3088,1903820,1024,31487⟩ = true := by decide
theorem row_cert_231 : quickRow ⟨3088,5770444,2064,47055⟩ = true := by decide
theorem row_cert_232 : quickRow ⟨3088,5786828,2048,14335⟩ = true := by decide
theorem row_cert_233 : quickRow ⟨3088,7867596,2064,30671⟩ = true := by decide
theorem row_cert_234 : quickRow ⟨3088,9964748,1040,31695⟩ = true := by decide
theorem row_cert_235 : quickRow ⟨3088,9964748,1040,64455⟩ = true := by decide
theorem row_cert_236 : quickRow ⟨3088,10128588,1024,31735⟩ = true := by decide
theorem row_cert_237 : quickRow ⟨3089,29491,3089,62446⟩ = true := by decide
theorem row_cert_238 : quickRow ⟨3090,1576140,3088,63438⟩ = true := by decide
theorem row_cert_239 : quickRow ⟨3091,5799935,2049,14334⟩ = true := by decide
theorem row_cert_240 : quickRow ⟨3092,1576140,3088,64247⟩ = true := by decide
theorem row_cert_241 : quickRow ⟨3096,8552721,3096,62439⟩ = true := by decide
theorem row_cert_242 : quickRow ⟨3100,10456541,1032,31479⟩ = true := by decide
theorem row_cert_243 : quickRow ⟨3120,14680064,3120,62415⟩ = true := by decide
theorem row_cert_244 : quickRow ⟨3328,327680,3328,62207⟩ = true := by decide
theorem row_cert_245 : quickRow ⟨3336,8880128,3336,62199⟩ = true := by decide
theorem row_cert_246 : quickRow ⟨3344,328226,3344,62191⟩ = true := by decide
theorem row_cert_247 : quickRow ⟨3352,8880947,3352,62183⟩ = true := by decide
theorem row_cert_248 : quickRow ⟨3600,1576140,3088,64207⟩ = true := by decide
theorem row_cert_249 : quickRow ⟨3860,10456814,1280,31479⟩ = true := by decide
theorem row_cert_250 : quickRow ⟨4096,192,4096,47103⟩ = true := by decide
theorem row_cert_251 : quickRow ⟨4096,2560,4096,56831⟩ = true := by decide
theorem row_cert_252 : quickRow ⟨4096,8192,4096,16383⟩ = true := by decide
theorem row_cert_253 : quickRow ⟨4096,8432,4096,49150⟩ = true := by decide
theorem row_cert_254 : quickRow ⟨4096,17152,4096,57311⟩ = true := by decide
theorem row_cert_255 : quickRow ⟨4096,20224,4096,57341⟩ = true := by decide
theorem quick_group_7 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (224+i.val))) = true := by
  fin_cases i
  · exact row_cert_224
  · exact row_cert_225
  · exact row_cert_226
  · exact row_cert_227
  · exact row_cert_228
  · exact row_cert_229
  · exact row_cert_230
  · exact row_cert_231
  · exact row_cert_232
  · exact row_cert_233
  · exact row_cert_234
  · exact row_cert_235
  · exact row_cert_236
  · exact row_cert_237
  · exact row_cert_238
  · exact row_cert_239
  · exact row_cert_240
  · exact row_cert_241
  · exact row_cert_242
  · exact row_cert_243
  · exact row_cert_244
  · exact row_cert_245
  · exact row_cert_246
  · exact row_cert_247
  · exact row_cert_248
  · exact row_cert_249
  · exact row_cert_250
  · exact row_cert_251
  · exact row_cert_252
  · exact row_cert_253
  · exact row_cert_254
  · exact row_cert_255
end G11GuardFront
