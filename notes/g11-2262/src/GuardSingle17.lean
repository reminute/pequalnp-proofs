import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_544 : quickRow ⟨52233,8880128,52233,29687⟩ = true := by decide
theorem row_cert_545 : quickRow ⟨52240,1576140,52240,13311⟩ = true := by decide
theorem row_cert_546 : quickRow ⟨52241,1576140,52241,13310⟩ = true := by decide
theorem row_cert_547 : quickRow ⟨52241,8880128,52241,29679⟩ = true := by decide
theorem row_cert_548 : quickRow ⟨52245,10456268,33792,31479⟩ = true := by decide
theorem row_cert_549 : quickRow ⟨52248,1576396,52232,13303⟩ = true := by decide
theorem row_cert_550 : quickRow ⟨52249,1576413,52233,13302⟩ = true := by decide
theorem row_cert_551 : quickRow ⟨52249,8880401,35864,29671⟩ = true := by decide
theorem row_cert_552 : quickRow ⟨52481,8880128,52481,29439⟩ = true := by decide
theorem row_cert_553 : quickRow ⟨52488,6320128,52488,13311⟩ = true := by decide
theorem row_cert_554 : quickRow ⟨52489,6320128,52489,13310⟩ = true := by decide
theorem row_cert_555 : quickRow ⟨52489,8880128,52489,29431⟩ = true := by decide
theorem row_cert_556 : quickRow ⟨52496,1576652,52480,13055⟩ = true := by decide
theorem row_cert_557 : quickRow ⟨52497,1576686,52481,13054⟩ = true := by decide
theorem row_cert_558 : quickRow ⟨52497,8880674,36112,29423⟩ = true := by decide
theorem row_cert_559 : quickRow ⟨52504,1576908,52488,13047⟩ = true := by decide
theorem row_cert_560 : quickRow ⟨52504,6320896,52240,13295⟩ = true := by decide
theorem row_cert_561 : quickRow ⟨52505,1576959,52489,13046⟩ = true := by decide
theorem row_cert_562 : quickRow ⟨52505,6320947,52241,13294⟩ = true := by decide
theorem row_cert_563 : quickRow ⟨52505,8880947,36120,29415⟩ = true := by decide
theorem row_cert_564 : quickRow ⟨53248,8192,53248,12287⟩ = true := by decide
theorem row_cert_565 : quickRow ⟨53249,8432,53249,12286⟩ = true := by decide
theorem row_cert_566 : quickRow ⟨53376,2109440,53376,12159⟩ = true := by decide
theorem row_cert_567 : quickRow ⟨53377,2109695,53377,12158⟩ = true := by decide
theorem row_cert_568 : quickRow ⟨54664,7372748,49152,14334⟩ = true := by decide
theorem row_cert_569 : quickRow ⟨55296,8384,55296,10239⟩ = true := by decide
theorem row_cert_570 : quickRow ⟨55297,8432,55297,10238⟩ = true := by decide
theorem row_cert_571 : quickRow ⟨55424,2633932,55424,10111⟩ = true := by decide
theorem row_cert_572 : quickRow ⟨55425,2633983,55425,10110⟩ = true := by decide
theorem row_cert_573 : quickRow ⟨59393,8880128,51201,45052⟩ = true := by decide
theorem quick_group_17 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (544+i.val))) = true := by
  fin_cases i
  · exact row_cert_544
  · exact row_cert_545
  · exact row_cert_546
  · exact row_cert_547
  · exact row_cert_548
  · exact row_cert_549
  · exact row_cert_550
  · exact row_cert_551
  · exact row_cert_552
  · exact row_cert_553
  · exact row_cert_554
  · exact row_cert_555
  · exact row_cert_556
  · exact row_cert_557
  · exact row_cert_558
  · exact row_cert_559
  · exact row_cert_560
  · exact row_cert_561
  · exact row_cert_562
  · exact row_cert_563
  · exact row_cert_564
  · exact row_cert_565
  · exact row_cert_566
  · exact row_cert_567
  · exact row_cert_568
  · exact row_cert_569
  · exact row_cert_570
  · exact row_cert_571
  · exact row_cert_572
  · exact row_cert_573
  · decide
  · decide
end G11GuardFront
