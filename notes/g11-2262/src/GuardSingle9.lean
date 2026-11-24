import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_288 : quickRow ⟨8738,16285701,8704,56763⟩ = true := by decide
theorem row_cert_289 : quickRow ⟨8738,16351232,8194,57276⟩ = true := by decide
theorem row_cert_290 : quickRow ⟨8738,16416768,514,65016⟩ = true := by decide
theorem row_cert_291 : quickRow ⟨8739,491520,8739,56796⟩ = true := by decide
theorem row_cert_292 : quickRow ⟨8740,164177,8740,56795⟩ = true := by decide
theorem row_cert_293 : quickRow ⟨8742,165205,8742,56793⟩ = true := by decide
theorem row_cert_294 : quickRow ⟨8746,16252928,8738,64763⟩ = true := by decide
theorem row_cert_295 : quickRow ⟨8752,2248,8752,56783⟩ = true := by decide
theorem row_cert_296 : quickRow ⟨8754,3276,8754,56781⟩ = true := by decide
theorem row_cert_297 : quickRow ⟨8768,65546,8768,56767⟩ = true := by decide
theorem row_cert_298 : quickRow ⟨8770,69647,8770,56765⟩ = true := by decide
theorem row_cert_299 : quickRow ⟨8800,102411,8800,56735⟩ = true := by decide
theorem row_cert_300 : quickRow ⟨8802,102415,8802,56733⟩ = true := by decide
theorem row_cert_301 : quickRow ⟨8866,16252928,8738,53183⟩ = true := by decide
theorem row_cert_302 : quickRow ⟨8960,8192,8960,56575⟩ = true := by decide
theorem row_cert_303 : quickRow ⟨8962,28672,8962,56573⟩ = true := by decide
theorem row_cert_304 : quickRow ⟨8964,139344,8964,56571⟩ = true := by decide
theorem row_cert_305 : quickRow ⟨8966,161109,8966,56569⟩ = true := by decide
theorem row_cert_306 : quickRow ⟨8992,28672,8992,56543⟩ = true := by decide
theorem row_cert_307 : quickRow ⟨8994,28672,8994,56541⟩ = true := by decide
theorem row_cert_308 : quickRow ⟨8996,192849,8996,56539⟩ = true := by decide
theorem row_cert_309 : quickRow ⟨8998,193877,8998,56537⟩ = true := by decide
theorem row_cert_310 : quickRow ⟨9762,16252928,8738,64719⟩ = true := by decide
theorem row_cert_311 : quickRow ⟨10240,8388800,0,45007⟩ = true := by decide
theorem row_cert_312 : quickRow ⟨10786,16252928,8738,65484⟩ = true := by decide
theorem row_cert_313 : quickRow ⟨12290,20224,12290,53245⟩ = true := by decide
theorem row_cert_314 : quickRow ⟨12320,17152,12320,53215⟩ = true := by decide
theorem row_cert_315 : quickRow ⟨12322,20224,12322,53213⟩ = true := by decide
theorem row_cert_316 : quickRow ⟨12352,404208,8256,56639⟩ = true := by decide
theorem row_cert_317 : quickRow ⟨12352,404218,8192,56829⟩ = true := by decide
theorem row_cert_318 : quickRow ⟨12352,405759,12288,53117⟩ = true := by decide
theorem row_cert_319 : quickRow ⟨12352,418800,8256,57119⟩ = true := by decide
theorem quick_group_9 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (288+i.val))) = true := by
  fin_cases i
  · exact row_cert_288
  · exact row_cert_289
  · exact row_cert_290
  · exact row_cert_291
  · exact row_cert_292
  · exact row_cert_293
  · exact row_cert_294
  · exact row_cert_295
  · exact row_cert_296
  · exact row_cert_297
  · exact row_cert_298
  · exact row_cert_299
  · exact row_cert_300
  · exact row_cert_301
  · exact row_cert_302
  · exact row_cert_303
  · exact row_cert_304
  · exact row_cert_305
  · exact row_cert_306
  · exact row_cert_307
  · exact row_cert_308
  · exact row_cert_309
  · exact row_cert_310
  · exact row_cert_311
  · exact row_cert_312
  · exact row_cert_313
  · exact row_cert_314
  · exact row_cert_315
  · exact row_cert_316
  · exact row_cert_317
  · exact row_cert_318
  · exact row_cert_319
end G11GuardFront
