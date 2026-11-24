import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_320 : quickRow ⟨12352,421872,8256,57149⟩ = true := by decide
theorem row_cert_321 : quickRow ⟨12352,422899,8192,57309⟩ = true := by decide
theorem row_cert_322 : quickRow ⟨12352,467184,12288,36351⟩ = true := by decide
theorem row_cert_323 : quickRow ⟨12352,467194,12288,52607⟩ = true := by decide
theorem row_cert_324 : quickRow ⟨12352,467698,8192,56799⟩ = true := by decide
theorem row_cert_325 : quickRow ⟨12352,499952,12288,36831⟩ = true := by decide
theorem row_cert_326 : quickRow ⟨12352,504051,12288,53087⟩ = true := by decide
theorem row_cert_327 : quickRow ⟨12352,8888560,4096,44927⟩ = true := by decide
theorem row_cert_328 : quickRow ⟨12353,401648,12352,36861⟩ = true := by decide
theorem row_cert_329 : quickRow ⟨12354,24335,12354,53181⟩ = true := by decide
theorem row_cert_330 : quickRow ⟨12355,491519,8194,56797⟩ = true := by decide
theorem row_cert_331 : quickRow ⟨12384,119555,12384,53151⟩ = true := by decide
theorem row_cert_332 : quickRow ⟨12386,122639,12386,53149⟩ = true := by decide
theorem row_cert_333 : quickRow ⟨12400,523259,8224,56797⟩ = true := by decide
theorem row_cert_334 : quickRow ⟨12416,11010048,12416,53119⟩ = true := by decide
theorem row_cert_335 : quickRow ⟨12480,401648,12480,61247⟩ = true := by decide
theorem row_cert_336 : quickRow ⟨12480,11112463,12480,53055⟩ = true := by decide
theorem row_cert_337 : quickRow ⟨12800,2560,12800,52735⟩ = true := by decide
theorem row_cert_338 : quickRow ⟨12802,20224,12802,52733⟩ = true := by decide
theorem row_cert_339 : quickRow ⟨12832,19200,12832,52703⟩ = true := by decide
theorem row_cert_340 : quickRow ⟨12834,20224,12834,52701⟩ = true := by decide
theorem row_cert_341 : quickRow ⟨12864,68106,12864,52671⟩ = true := by decide
theorem row_cert_342 : quickRow ⟨12866,89871,12866,52669⟩ = true := by decide
theorem row_cert_343 : quickRow ⟨12896,121611,12896,52639⟩ = true := by decide
theorem row_cert_344 : quickRow ⟨12898,122639,12898,52637⟩ = true := by decide
theorem row_cert_345 : quickRow ⟨13124,490491,8704,56797⟩ = true := by decide
theorem row_cert_346 : quickRow ⟨16384,2560,16384,32511⟩ = true := by decide
theorem row_cert_347 : quickRow ⟨16384,17152,16384,63471⟩ = true := by decide
theorem row_cert_348 : quickRow ⟨16384,393216,16384,65343⟩ = true := by decide
theorem row_cert_349 : quickRow ⟨16384,1049856,16384,32759⟩ = true := by decide
theorem row_cert_350 : quickRow ⟨16384,1051648,16384,31743⟩ = true := by decide
theorem row_cert_351 : quickRow ⟨16384,4210688,16384,62463⟩ = true := by decide
theorem quick_group_10 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (320+i.val))) = true := by
  fin_cases i
  · exact row_cert_320
  · exact row_cert_321
  · exact row_cert_322
  · exact row_cert_323
  · exact row_cert_324
  · exact row_cert_325
  · exact row_cert_326
  · exact row_cert_327
  · exact row_cert_328
  · exact row_cert_329
  · exact row_cert_330
  · exact row_cert_331
  · exact row_cert_332
  · exact row_cert_333
  · exact row_cert_334
  · exact row_cert_335
  · exact row_cert_336
  · exact row_cert_337
  · exact row_cert_338
  · exact row_cert_339
  · exact row_cert_340
  · exact row_cert_341
  · exact row_cert_342
  · exact row_cert_343
  · exact row_cert_344
  · exact row_cert_345
  · exact row_cert_346
  · exact row_cert_347
  · exact row_cert_348
  · exact row_cert_349
  · exact row_cert_350
  · exact row_cert_351
end G11GuardFront
