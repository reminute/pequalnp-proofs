import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_352 : quickRow ⟨16384,5242880,16384,65532⟩ = true := by decide
theorem row_cert_353 : quickRow ⟨16384,8388608,16384,53247⟩ = true := by decide
theorem row_cert_354 : quickRow ⟨16384,8486912,16384,61375⟩ = true := by decide
theorem row_cert_355 : quickRow ⟨16387,5242880,16387,49148⟩ = true := by decide
theorem row_cert_356 : quickRow ⟨16416,8405760,0,51183⟩ = true := by decide
theorem row_cert_357 : quickRow ⟨16513,4111,16513,49022⟩ = true := by decide
theorem row_cert_358 : quickRow ⟨16576,393216,16576,48959⟩ = true := by decide
theorem row_cert_359 : quickRow ⟨16896,8391168,0,20223⟩ = true := by decide
theorem row_cert_360 : quickRow ⟨18435,5767168,18435,47100⟩ = true := by decide
theorem row_cert_361 : quickRow ⟨18448,17152,18448,47087⟩ = true := by decide
theorem row_cert_362 : quickRow ⟨18449,29491,18449,47086⟩ = true := by decide
theorem row_cert_363 : quickRow ⟨18560,524300,18560,46975⟩ = true := by decide
theorem row_cert_364 : quickRow ⟨18561,528399,18561,46974⟩ = true := by decide
theorem row_cert_365 : quickRow ⟨19456,4210688,19456,46079⟩ = true := by decide
theorem row_cert_366 : quickRow ⟨19457,4222976,19457,46078⟩ = true := by decide
theorem row_cert_367 : quickRow ⟨19472,4211456,19472,46063⟩ = true := by decide
theorem row_cert_368 : quickRow ⟨19473,4223795,19473,46062⟩ = true := by decide
theorem row_cert_369 : quickRow ⟨20481,8432,20481,45054⟩ = true := by decide
theorem row_cert_370 : quickRow ⟨20544,8486912,20544,44991⟩ = true := by decide
theorem row_cert_371 : quickRow ⟨20608,5263296,16512,46911⟩ = true := by decide
theorem row_cert_372 : quickRow ⟨20608,5263308,16384,47102⟩ = true := by decide
theorem row_cert_373 : quickRow ⟨20608,5267215,20480,44990⟩ = true := by decide
theorem row_cert_374 : quickRow ⟨20608,5271296,16512,16191⟩ = true := by decide
theorem row_cert_375 : quickRow ⟨20608,5271536,16512,48958⟩ = true := by decide
theorem row_cert_376 : quickRow ⟨20608,5275392,16384,16382⟩ = true := by decide
theorem row_cert_377 : quickRow ⟨20608,5787392,20480,34815⟩ = true := by decide
theorem row_cert_378 : quickRow ⟨20608,5787404,20480,42943⟩ = true := by decide
theorem row_cert_379 : quickRow ⟨20608,7360256,20480,4095⟩ = true := by decide
theorem row_cert_380 : quickRow ⟨20608,7364352,20480,12223⟩ = true := by decide
theorem row_cert_381 : quickRow ⟨20608,16273152,4096,53183⟩ = true := by decide
theorem row_cert_382 : quickRow ⟨20609,12543,20609,44926⟩ = true := by decide
theorem row_cert_383 : quickRow ⟨20610,5263104,20608,36862⟩ = true := by decide
theorem quick_group_11 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (352+i.val))) = true := by
  fin_cases i
  · exact row_cert_352
  · exact row_cert_353
  · exact row_cert_354
  · exact row_cert_355
  · exact row_cert_356
  · exact row_cert_357
  · exact row_cert_358
  · exact row_cert_359
  · exact row_cert_360
  · exact row_cert_361
  · exact row_cert_362
  · exact row_cert_363
  · exact row_cert_364
  · exact row_cert_365
  · exact row_cert_366
  · exact row_cert_367
  · exact row_cert_368
  · exact row_cert_369
  · exact row_cert_370
  · exact row_cert_371
  · exact row_cert_372
  · exact row_cert_373
  · exact row_cert_374
  · exact row_cert_375
  · exact row_cert_376
  · exact row_cert_377
  · exact row_cert_378
  · exact row_cert_379
  · exact row_cert_380
  · exact row_cert_381
  · exact row_cert_382
  · exact row_cert_383
end G11GuardFront
