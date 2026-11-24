import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_480 : quickRow ⟨36105,6320128,36105,29694⟩ = true := by decide
theorem row_cert_481 : quickRow ⟨36112,1576140,36112,29439⟩ = true := by decide
theorem row_cert_482 : quickRow ⟨36113,1576686,36097,29438⟩ = true := by decide
theorem row_cert_483 : quickRow ⟨36120,1576140,36120,29431⟩ = true := by decide
theorem row_cert_484 : quickRow ⟨36120,6320128,36120,29679⟩ = true := by decide
theorem row_cert_485 : quickRow ⟨36120,7897036,34816,14334⟩ = true := by decide
theorem row_cert_486 : quickRow ⟨36121,1576959,36105,29430⟩ = true := by decide
theorem row_cert_487 : quickRow ⟨36121,6320947,35857,29678⟩ = true := by decide
theorem row_cert_488 : quickRow ⟨40960,8396800,0,44287⟩ = true := by decide
theorem row_cert_489 : quickRow ⟨41506,16252928,8738,64764⟩ = true := by decide
theorem row_cert_490 : quickRow ⟨49155,7340032,49155,16380⟩ = true := by decide
theorem row_cert_491 : quickRow ⟨49160,1049856,49160,16375⟩ = true := by decide
theorem row_cert_492 : quickRow ⟨49161,1049941,49161,16374⟩ = true := by decide
theorem row_cert_493 : quickRow ⟨49280,2101248,49280,16255⟩ = true := by decide
theorem row_cert_494 : quickRow ⟨49281,2101263,49281,16254⟩ = true := by decide
theorem row_cert_495 : quickRow ⟨49408,2560,49408,16127⟩ = true := by decide
theorem row_cert_496 : quickRow ⟨49409,2730,49409,16126⟩ = true := by decide
theorem row_cert_497 : quickRow ⟨49416,1052416,49416,16119⟩ = true := by decide
theorem row_cert_498 : quickRow ⟨49417,1052671,49417,16118⟩ = true := by decide
theorem row_cert_499 : quickRow ⟨50176,1051648,50176,15359⟩ = true := by decide
theorem row_cert_500 : quickRow ⟨50177,1051852,50177,15358⟩ = true := by decide
theorem row_cert_501 : quickRow ⟨50184,1051904,50184,15351⟩ = true := by decide
theorem row_cert_502 : quickRow ⟨50185,1052125,50185,15350⟩ = true := by decide
theorem row_cert_503 : quickRow ⟨50432,1052160,50432,15103⟩ = true := by decide
theorem row_cert_504 : quickRow ⟨50433,1052398,50433,15102⟩ = true := by decide
theorem row_cert_505 : quickRow ⟨50440,1052416,50440,15095⟩ = true := by decide
theorem row_cert_506 : quickRow ⟨50441,1052671,50441,15094⟩ = true := by decide
theorem row_cert_507 : quickRow ⟨51201,8880138,49152,15999⟩ = true := by decide
theorem row_cert_508 : quickRow ⟨51201,8880208,49152,12279⟩ = true := by decide
theorem row_cert_509 : quickRow ⟨51201,8880288,49152,12031⟩ = true := by decide
theorem row_cert_510 : quickRow ⟨51201,8880320,49152,11263⟩ = true := by decide
theorem row_cert_511 : quickRow ⟨51201,8880401,34816,30695⟩ = true := by decide
theorem quick_group_15 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (480+i.val))) = true := by
  fin_cases i
  · exact row_cert_480
  · exact row_cert_481
  · exact row_cert_482
  · exact row_cert_483
  · exact row_cert_484
  · exact row_cert_485
  · exact row_cert_486
  · exact row_cert_487
  · exact row_cert_488
  · exact row_cert_489
  · exact row_cert_490
  · exact row_cert_491
  · exact row_cert_492
  · exact row_cert_493
  · exact row_cert_494
  · exact row_cert_495
  · exact row_cert_496
  · exact row_cert_497
  · exact row_cert_498
  · exact row_cert_499
  · exact row_cert_500
  · exact row_cert_501
  · exact row_cert_502
  · exact row_cert_503
  · exact row_cert_504
  · exact row_cert_505
  · exact row_cert_506
  · exact row_cert_507
  · exact row_cert_508
  · exact row_cert_509
  · exact row_cert_510
  · exact row_cert_511
end G11GuardFront
