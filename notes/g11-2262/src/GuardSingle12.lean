import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_384 : quickRow ⟨20672,5263104,20672,61247⟩ = true := by decide
theorem row_cert_385 : quickRow ⟨20672,11112463,20672,44863⟩ = true := by decide
theorem row_cert_386 : quickRow ⟨21632,5263104,20608,14335⟩ = true := by decide
theorem row_cert_387 : quickRow ⟨21635,5275647,16385,14334⟩ = true := by decide
theorem row_cert_388 : quickRow ⟨22528,192,22528,43007⟩ = true := by decide
theorem row_cert_389 : quickRow ⟨22529,8432,22529,43006⟩ = true := by decide
theorem row_cert_390 : quickRow ⟨22656,524492,22656,42879⟩ = true := by decide
theorem row_cert_391 : quickRow ⟨22657,536831,22657,42878⟩ = true := by decide
theorem row_cert_392 : quickRow ⟨23696,5799884,18432,14334⟩ = true := by decide
theorem row_cert_393 : quickRow ⟨24576,5636096,0,65340⟩ = true := by decide
theorem row_cert_394 : quickRow ⟨25122,16252928,8738,53244⟩ = true := by decide
theorem row_cert_395 : quickRow ⟨28672,8388608,28672,36863⟩ = true := by decide
theorem row_cert_396 : quickRow ⟨28736,8486912,28736,36799⟩ = true := by decide
theorem row_cert_397 : quickRow ⟨28800,11010048,28800,36735⟩ = true := by decide
theorem row_cert_398 : quickRow ⟨28864,401648,28864,44863⟩ = true := by decide
theorem row_cert_399 : quickRow ⟨28864,5263104,28864,53055⟩ = true := by decide
theorem row_cert_400 : quickRow ⟨28864,11112463,28864,36671⟩ = true := by decide
theorem row_cert_401 : quickRow ⟨32768,8192,32768,45055⟩ = true := by decide
theorem row_cert_402 : quickRow ⟨32768,28672,32768,63471⟩ = true := by decide
theorem row_cert_403 : quickRow ⟨32768,327680,32768,65523⟩ = true := by decide
theorem row_cert_404 : quickRow ⟨32768,491520,32768,64495⟩ = true := by decide
theorem row_cert_405 : quickRow ⟨32768,2101248,32768,49023⟩ = true := by decide
theorem row_cert_406 : quickRow ⟨32768,6291456,32768,65532⟩ = true := by decide
theorem row_cert_407 : quickRow ⟨32768,8388608,32768,64767⟩ = true := by decide
theorem row_cert_408 : quickRow ⟨32768,8552448,32768,65275⟩ = true := by decide
theorem row_cert_409 : quickRow ⟨32771,6291456,32771,32764⟩ = true := by decide
theorem row_cert_410 : quickRow ⟨32777,1365,32777,32758⟩ = true := by decide
theorem row_cert_411 : quickRow ⟨32780,327680,32780,32755⟩ = true := by decide
theorem row_cert_412 : quickRow ⟨32800,6782976,0,64492⟩ = true := by decide
theorem row_cert_413 : quickRow ⟨32800,8417280,0,62703⟩ = true := by decide
theorem row_cert_414 : quickRow ⟨32816,521011,48,62447⟩ = true := by decide
theorem row_cert_415 : quickRow ⟨33025,2730,33025,32510⟩ = true := by decide
theorem quick_group_12 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (384+i.val))) = true := by
  fin_cases i
  · exact row_cert_384
  · exact row_cert_385
  · exact row_cert_386
  · exact row_cert_387
  · exact row_cert_388
  · exact row_cert_389
  · exact row_cert_390
  · exact row_cert_391
  · exact row_cert_392
  · exact row_cert_393
  · exact row_cert_394
  · exact row_cert_395
  · exact row_cert_396
  · exact row_cert_397
  · exact row_cert_398
  · exact row_cert_399
  · exact row_cert_400
  · exact row_cert_401
  · exact row_cert_402
  · exact row_cert_403
  · exact row_cert_404
  · exact row_cert_405
  · exact row_cert_406
  · exact row_cert_407
  · exact row_cert_408
  · exact row_cert_409
  · exact row_cert_410
  · exact row_cert_411
  · exact row_cert_412
  · exact row_cert_413
  · exact row_cert_414
  · exact row_cert_415
end G11GuardFront
