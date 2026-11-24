import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_512 : quickRow ⟨51201,8880674,34816,30447⟩ = true := by decide
theorem row_cert_513 : quickRow ⟨51201,8882312,32768,31487⟩ = true := by decide
theorem row_cert_514 : quickRow ⟨51201,8884227,18432,46959⟩ = true := by decide
theorem row_cert_515 : quickRow ⟨51201,8888320,18432,41983⟩ = true := by decide
theorem row_cert_516 : quickRow ⟨51201,8888368,18432,42991⟩ = true := by decide
theorem row_cert_517 : quickRow ⟨51201,8908800,2048,62447⟩ = true := by decide
theorem row_cert_518 : quickRow ⟨51201,9404421,49152,16247⟩ = true := by decide
theorem row_cert_519 : quickRow ⟨51201,9404428,49152,15231⟩ = true := by decide
theorem row_cert_520 : quickRow ⟨51201,10452992,32769,31740⟩ = true := by decide
theorem row_cert_521 : quickRow ⟨51201,10452992,32769,32756⟩ = true := by decide
theorem row_cert_522 : quickRow ⟨51201,10454084,32768,31735⟩ = true := by decide
theorem row_cert_523 : quickRow ⟨51201,10981376,18432,45951⟩ = true := by decide
theorem row_cert_524 : quickRow ⟨51201,11501568,16385,49020⟩ = true := by decide
theorem row_cert_525 : quickRow ⟨51201,15171584,2049,62460⟩ = true := by decide
theorem row_cert_526 : quickRow ⟨51203,7864320,51203,14332⟩ = true := by decide
theorem row_cert_527 : quickRow ⟨51205,8880128,51201,32503⟩ = true := by decide
theorem row_cert_528 : quickRow ⟨51208,1574212,51208,14327⟩ = true := by decide
theorem row_cert_529 : quickRow ⟨51209,1574229,51209,14326⟩ = true := by decide
theorem row_cert_530 : quickRow ⟨51213,10456541,32776,31479⟩ = true := by decide
theorem row_cert_531 : quickRow ⟨51216,29440,51216,14319⟩ = true := by decide
theorem row_cert_532 : quickRow ⟨51217,29491,51217,14318⟩ = true := by decide
theorem row_cert_533 : quickRow ⟨51233,8880128,51201,63468⟩ = true := by decide
theorem row_cert_534 : quickRow ⟨51265,8880128,51201,44927⟩ = true := by decide
theorem row_cert_535 : quickRow ⟨51328,2625548,51328,14207⟩ = true := by decide
theorem row_cert_536 : quickRow ⟨51329,2625551,51329,14206⟩ = true := by decide
theorem row_cert_537 : quickRow ⟨51456,2696,51456,14079⟩ = true := by decide
theorem row_cert_538 : quickRow ⟨51457,2730,51457,14078⟩ = true := by decide
theorem row_cert_539 : quickRow ⟨51464,1576908,51464,14071⟩ = true := by decide
theorem row_cert_540 : quickRow ⟨51465,1576959,51465,14070⟩ = true := by decide
theorem row_cert_541 : quickRow ⟨51713,8880128,51201,32508⟩ = true := by decide
theorem row_cert_542 : quickRow ⟨51973,10456814,33024,31479⟩ = true := by decide
theorem row_cert_543 : quickRow ⟨52225,8880128,52225,29695⟩ = true := by decide
theorem quick_group_16 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (512+i.val))) = true := by
  fin_cases i
  · exact row_cert_512
  · exact row_cert_513
  · exact row_cert_514
  · exact row_cert_515
  · exact row_cert_516
  · exact row_cert_517
  · exact row_cert_518
  · exact row_cert_519
  · exact row_cert_520
  · exact row_cert_521
  · exact row_cert_522
  · exact row_cert_523
  · exact row_cert_524
  · exact row_cert_525
  · exact row_cert_526
  · exact row_cert_527
  · exact row_cert_528
  · exact row_cert_529
  · exact row_cert_530
  · exact row_cert_531
  · exact row_cert_532
  · exact row_cert_533
  · exact row_cert_534
  · exact row_cert_535
  · exact row_cert_536
  · exact row_cert_537
  · exact row_cert_538
  · exact row_cert_539
  · exact row_cert_540
  · exact row_cert_541
  · exact row_cert_542
  · exact row_cert_543
end G11GuardFront
