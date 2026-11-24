import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_416 : quickRow ⟨33028,8552448,33028,32507⟩ = true := by decide
theorem row_cert_417 : quickRow ⟨33033,4095,33033,32502⟩ = true := by decide
theorem row_cert_418 : quickRow ⟨33036,10126677,33036,32499⟩ = true := by decide
theorem row_cert_419 : quickRow ⟨33280,6619136,0,65520⟩ = true := by decide
theorem row_cert_420 : quickRow ⟨33536,8388608,33536,31999⟩ = true := by decide
theorem row_cert_421 : quickRow ⟨33540,8552448,33540,31995⟩ = true := by decide
theorem row_cert_422 : quickRow ⟨33544,9961472,33544,31991⟩ = true := by decide
theorem row_cert_423 : quickRow ⟨33548,330410,33548,32499⟩ = true := by decide
theorem row_cert_424 : quickRow ⟨33548,10126677,33548,31987⟩ = true := by decide
theorem row_cert_425 : quickRow ⟨33793,3276,33793,31742⟩ = true := by decide
theorem row_cert_426 : quickRow ⟨33801,3549,33801,31734⟩ = true := by decide
theorem row_cert_427 : quickRow ⟨33804,329864,33804,31731⟩ = true := by decide
theorem row_cert_428 : quickRow ⟨33808,491520,33808,31727⟩ = true := by decide
theorem row_cert_429 : quickRow ⟨33816,491793,33816,31719⟩ = true := by decide
theorem row_cert_430 : quickRow ⟨34049,3822,34049,31486⟩ = true := by decide
theorem row_cert_431 : quickRow ⟨34052,10126404,34052,31483⟩ = true := by decide
theorem row_cert_432 : quickRow ⟨34056,6320896,33792,15343⟩ = true := by decide
theorem row_cert_433 : quickRow ⟨34056,6320947,33792,31726⟩ = true := by decide
theorem row_cert_434 : quickRow ⟨34056,6321493,33024,32506⟩ = true := by decide
theorem row_cert_435 : quickRow ⟨34056,6322312,32776,30707⟩ = true := by decide
theorem row_cert_436 : quickRow ⟨34056,6322688,32776,16371⟩ = true := by decide
theorem row_cert_437 : quickRow ⟨34056,6322858,32776,32754⟩ = true := by decide
theorem row_cert_438 : quickRow ⟨34056,6323404,32768,30718⟩ = true := by decide
theorem row_cert_439 : quickRow ⟨34056,6323968,32768,16382⟩ = true := by decide
theorem row_cert_440 : quickRow ⟨34056,6484241,1280,64235⟩ = true := by decide
theorem row_cert_441 : quickRow ⟨34056,6647808,1032,62451⟩ = true := by decide
theorem row_cert_442 : quickRow ⟨34056,6648354,1032,64483⟩ = true := by decide
theorem row_cert_443 : quickRow ⟨34056,6811648,1024,62447⟩ = true := by decide
theorem row_cert_444 : quickRow ⟨34056,7368704,33024,15615⟩ = true := by decide
theorem row_cert_445 : quickRow ⟨34056,7369984,33024,16123⟩ = true := by decide
theorem row_cert_446 : quickRow ⟨34056,7371776,32768,14335⟩ = true := by decide
theorem row_cert_447 : quickRow ⟨34056,7892992,33024,29951⟩ = true := by decide
theorem quick_group_13 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (416+i.val))) = true := by
  fin_cases i
  · exact row_cert_416
  · exact row_cert_417
  · exact row_cert_418
  · exact row_cert_419
  · exact row_cert_420
  · exact row_cert_421
  · exact row_cert_422
  · exact row_cert_423
  · exact row_cert_424
  · exact row_cert_425
  · exact row_cert_426
  · exact row_cert_427
  · exact row_cert_428
  · exact row_cert_429
  · exact row_cert_430
  · exact row_cert_431
  · exact row_cert_432
  · exact row_cert_433
  · exact row_cert_434
  · exact row_cert_435
  · exact row_cert_436
  · exact row_cert_437
  · exact row_cert_438
  · exact row_cert_439
  · exact row_cert_440
  · exact row_cert_441
  · exact row_cert_442
  · exact row_cert_443
  · exact row_cert_444
  · exact row_cert_445
  · exact row_cert_446
  · exact row_cert_447
end G11GuardFront
