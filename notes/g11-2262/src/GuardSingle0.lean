import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_0 : quickRow ⟨0,192,0,65535⟩ = true := by decide
theorem row_cert_1 : quickRow ⟨0,1365,0,65535⟩ = true := by decide
theorem row_cert_2 : quickRow ⟨0,2184,0,65535⟩ = true := by decide
theorem row_cert_3 : quickRow ⟨0,2560,0,65535⟩ = true := by decide
theorem row_cert_4 : quickRow ⟨0,4111,0,65535⟩ = true := by decide
theorem row_cert_5 : quickRow ⟨0,8192,0,65535⟩ = true := by decide
theorem row_cert_6 : quickRow ⟨0,17152,0,65535⟩ = true := by decide
theorem row_cert_7 : quickRow ⟨0,65546,0,65535⟩ = true := by decide
theorem row_cert_8 : quickRow ⟨0,102403,0,65535⟩ = true := by decide
theorem row_cert_9 : quickRow ⟨0,131152,0,65535⟩ = true := by decide
theorem row_cert_10 : quickRow ⟨0,164113,0,65535⟩ = true := by decide
theorem row_cert_11 : quickRow ⟨0,262304,0,65535⟩ = true := by decide
theorem row_cert_12 : quickRow ⟨0,327680,0,65535⟩ = true := by decide
theorem row_cert_13 : quickRow ⟨0,393216,0,65535⟩ = true := by decide
theorem row_cert_14 : quickRow ⟨0,524300,0,65535⟩ = true := by decide
theorem row_cert_15 : quickRow ⟨0,1049856,0,65535⟩ = true := by decide
theorem row_cert_16 : quickRow ⟨0,1051648,0,65535⟩ = true := by decide
theorem row_cert_17 : quickRow ⟨0,1572864,0,65535⟩ = true := by decide
theorem row_cert_18 : quickRow ⟨0,2101248,0,65535⟩ = true := by decide
theorem row_cert_19 : quickRow ⟨0,4210688,0,65535⟩ = true := by decide
theorem row_cert_20 : quickRow ⟨0,5242880,0,65535⟩ = true := by decide
theorem row_cert_21 : quickRow ⟨0,6291456,0,65535⟩ = true := by decide
theorem row_cert_22 : quickRow ⟨0,8388608,0,65535⟩ = true := by decide
theorem row_cert_23 : quickRow ⟨1,1365,1,32759⟩ = true := by decide
theorem row_cert_24 : quickRow ⟨1,2730,1,32511⟩ = true := by decide
theorem row_cert_25 : quickRow ⟨1,3276,1,31743⟩ = true := by decide
theorem row_cert_26 : quickRow ⟨1,4111,1,49023⟩ = true := by decide
theorem row_cert_27 : quickRow ⟨1,8432,1,45055⟩ = true := by decide
theorem row_cert_28 : quickRow ⟨1,28672,1,62463⟩ = true := by decide
theorem row_cert_29 : quickRow ⟨1,29491,1,63471⟩ = true := by decide
theorem row_cert_30 : quickRow ⟨1,327680,1,65021⟩ = true := by decide
theorem row_cert_31 : quickRow ⟨1,393216,1,57341⟩ = true := by decide
theorem quick_group_0 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (0+i.val))) = true := by
  fin_cases i
  · exact row_cert_0
  · exact row_cert_1
  · exact row_cert_2
  · exact row_cert_3
  · exact row_cert_4
  · exact row_cert_5
  · exact row_cert_6
  · exact row_cert_7
  · exact row_cert_8
  · exact row_cert_9
  · exact row_cert_10
  · exact row_cert_11
  · exact row_cert_12
  · exact row_cert_13
  · exact row_cert_14
  · exact row_cert_15
  · exact row_cert_16
  · exact row_cert_17
  · exact row_cert_18
  · exact row_cert_19
  · exact row_cert_20
  · exact row_cert_21
  · exact row_cert_22
  · exact row_cert_23
  · exact row_cert_24
  · exact row_cert_25
  · exact row_cert_26
  · exact row_cert_27
  · exact row_cert_28
  · exact row_cert_29
  · exact row_cert_30
  · exact row_cert_31
end G11GuardFront
