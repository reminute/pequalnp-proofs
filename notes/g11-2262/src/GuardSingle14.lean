import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_448 : quickRow ⟨34056,7894084,33024,30459⟩ = true := by decide
theorem row_cert_449 : quickRow ⟨34056,14708736,1280,61695⟩ = true := by decide
theorem row_cert_450 : quickRow ⟨34056,14872576,1280,62203⟩ = true := by decide
theorem row_cert_451 : quickRow ⟨34056,16281600,256,64763⟩ = true := by decide
theorem row_cert_452 : quickRow ⟨34057,4095,34057,31478⟩ = true := by decide
theorem row_cert_453 : quickRow ⟨34058,6320128,34056,31998⟩ = true := by decide
theorem row_cert_454 : quickRow ⟨34059,7372799,32769,14334⟩ = true := by decide
theorem row_cert_455 : quickRow ⟨34060,6320128,34060,65267⟩ = true := by decide
theorem row_cert_456 : quickRow ⟨34060,10126677,34060,31475⟩ = true := by decide
theorem row_cert_457 : quickRow ⟨34064,492066,34064,31471⟩ = true := by decide
theorem row_cert_458 : quickRow ⟨34072,492339,34072,31463⟩ = true := by decide
theorem row_cert_459 : quickRow ⟨34088,6320128,34056,63727⟩ = true := by decide
theorem row_cert_460 : quickRow ⟨34560,9961472,34560,30975⟩ = true := by decide
theorem row_cert_461 : quickRow ⟨34564,10126404,34564,30971⟩ = true := by decide
theorem row_cert_462 : quickRow ⟨34568,9961472,34568,30967⟩ = true := by decide
theorem row_cert_463 : quickRow ⟨34572,330410,34572,31475⟩ = true := by decide
theorem row_cert_464 : quickRow ⟨34572,6320128,34572,64755⟩ = true := by decide
theorem row_cert_465 : quickRow ⟨34572,10126677,34572,30963⟩ = true := by decide
theorem row_cert_466 : quickRow ⟨34819,7864320,34819,30716⟩ = true := by decide
theorem row_cert_467 : quickRow ⟨34824,1573956,34824,30711⟩ = true := by decide
theorem row_cert_468 : quickRow ⟨34825,1574229,34825,30710⟩ = true := by decide
theorem row_cert_469 : quickRow ⟨34832,28672,34832,30703⟩ = true := by decide
theorem row_cert_470 : quickRow ⟨34833,29491,34833,30702⟩ = true := by decide
theorem row_cert_471 : quickRow ⟨35072,2184,35072,30463⟩ = true := by decide
theorem row_cert_472 : quickRow ⟨35073,2730,35073,30462⟩ = true := by decide
theorem row_cert_473 : quickRow ⟨35080,1576140,35080,30455⟩ = true := by decide
theorem row_cert_474 : quickRow ⟨35081,1576959,35081,30454⟩ = true := by decide
theorem row_cert_475 : quickRow ⟨35856,1576140,35856,29695⟩ = true := by decide
theorem row_cert_476 : quickRow ⟨35857,1576140,35857,29694⟩ = true := by decide
theorem row_cert_477 : quickRow ⟨35864,1576140,35864,29687⟩ = true := by decide
theorem row_cert_478 : quickRow ⟨35865,1576413,35849,29686⟩ = true := by decide
theorem row_cert_479 : quickRow ⟨36104,6320128,36104,29695⟩ = true := by decide
theorem quick_group_14 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (448+i.val))) = true := by
  fin_cases i
  · exact row_cert_448
  · exact row_cert_449
  · exact row_cert_450
  · exact row_cert_451
  · exact row_cert_452
  · exact row_cert_453
  · exact row_cert_454
  · exact row_cert_455
  · exact row_cert_456
  · exact row_cert_457
  · exact row_cert_458
  · exact row_cert_459
  · exact row_cert_460
  · exact row_cert_461
  · exact row_cert_462
  · exact row_cert_463
  · exact row_cert_464
  · exact row_cert_465
  · exact row_cert_466
  · exact row_cert_467
  · exact row_cert_468
  · exact row_cert_469
  · exact row_cert_470
  · exact row_cert_471
  · exact row_cert_472
  · exact row_cert_473
  · exact row_cert_474
  · exact row_cert_475
  · exact row_cert_476
  · exact row_cert_477
  · exact row_cert_478
  · exact row_cert_479
end G11GuardFront
