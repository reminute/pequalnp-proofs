import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_256 : quickRow ⟨4099,32767,3,40956⟩ = true := by decide
theorem row_cert_257 : quickRow ⟨4112,17344,0,38879⟩ = true := by decide
theorem row_cert_258 : quickRow ⟨4115,32767,3,38876⟩ = true := by decide
theorem row_cert_259 : quickRow ⟨4288,11112463,4288,61247⟩ = true := by decide
theorem row_cert_260 : quickRow ⟨4352,10752,0,7679⟩ = true := by decide
theorem row_cert_261 : quickRow ⟨4355,32767,3,7676⟩ = true := by decide
theorem row_cert_262 : quickRow ⟨4368,31688,0,5599⟩ = true := by decide
theorem row_cert_263 : quickRow ⟨4371,32767,3,5596⟩ = true := by decide
theorem row_cert_264 : quickRow ⟨8192,192,8192,65487⟩ = true := by decide
theorem row_cert_265 : quickRow ⟨8192,8192,8192,64767⟩ = true := by decide
theorem row_cert_266 : quickRow ⟨8192,131152,8192,65019⟩ = true := by decide
theorem row_cert_267 : quickRow ⟨8192,393216,8192,65532⟩ = true := by decide
theorem row_cert_268 : quickRow ⟨8192,5242880,8192,65343⟩ = true := by decide
theorem row_cert_269 : quickRow ⟨8192,8388608,8192,45055⟩ = true := by decide
theorem row_cert_270 : quickRow ⟨8192,11010048,8192,61311⟩ = true := by decide
theorem row_cert_271 : quickRow ⟨8195,393216,8195,57340⟩ = true := by decide
theorem row_cert_272 : quickRow ⟨8227,491520,8227,57308⟩ = true := by decide
theorem row_cert_273 : quickRow ⟨8240,192,8240,57295⟩ = true := by decide
theorem row_cert_274 : quickRow ⟨8242,3276,8242,57293⟩ = true := by decide
theorem row_cert_275 : quickRow ⟨8258,4111,8258,57277⟩ = true := by decide
theorem row_cert_276 : quickRow ⟨8288,102403,8288,57247⟩ = true := by decide
theorem row_cert_277 : quickRow ⟨8290,102415,8290,57245⟩ = true := by decide
theorem row_cert_278 : quickRow ⟨8384,5242880,8384,57151⟩ = true := by decide
theorem row_cert_279 : quickRow ⟨8707,458752,8707,56828⟩ = true := by decide
theorem row_cert_280 : quickRow ⟨8708,131152,8708,56827⟩ = true := by decide
theorem row_cert_281 : quickRow ⟨8710,132437,8710,56825⟩ = true := by decide
theorem row_cert_282 : quickRow ⟨8738,16252940,8224,57231⟩ = true := by decide
theorem row_cert_283 : quickRow ⟨8738,16254020,544,64971⟩ = true := by decide
theorem row_cert_284 : quickRow ⟨8738,16254208,8704,52731⟩ = true := by decide
theorem row_cert_285 : quickRow ⟨8738,16256000,8224,53199⟩ = true := by decide
theorem row_cert_286 : quickRow ⟨8738,16257024,8704,56511⟩ = true := by decide
theorem row_cert_287 : quickRow ⟨8738,16269312,8704,52479⟩ = true := by decide
theorem quick_group_8 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (256+i.val))) = true := by
  fin_cases i
  · exact row_cert_256
  · exact row_cert_257
  · exact row_cert_258
  · exact row_cert_259
  · exact row_cert_260
  · exact row_cert_261
  · exact row_cert_262
  · exact row_cert_263
  · exact row_cert_264
  · exact row_cert_265
  · exact row_cert_266
  · exact row_cert_267
  · exact row_cert_268
  · exact row_cert_269
  · exact row_cert_270
  · exact row_cert_271
  · exact row_cert_272
  · exact row_cert_273
  · exact row_cert_274
  · exact row_cert_275
  · exact row_cert_276
  · exact row_cert_277
  · exact row_cert_278
  · exact row_cert_279
  · exact row_cert_280
  · exact row_cert_281
  · exact row_cert_282
  · exact row_cert_283
  · exact row_cert_284
  · exact row_cert_285
  · exact row_cert_286
  · exact row_cert_287
end G11GuardFront
