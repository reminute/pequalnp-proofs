import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_32 : quickRow ⟨1,491520,1,65501⟩ = true := by decide
theorem row_cert_33 : quickRow ⟨2,1365,2,65019⟩ = true := by decide
theorem row_cert_34 : quickRow ⟨2,3276,2,65487⟩ = true := by decide
theorem row_cert_35 : quickRow ⟨2,4111,2,57279⟩ = true := by decide
theorem row_cert_36 : quickRow ⟨2,20224,2,53247⟩ = true := by decide
theorem row_cert_37 : quickRow ⟨2,28672,2,64767⟩ = true := by decide
theorem row_cert_38 : quickRow ⟨2,1572864,2,63486⟩ = true := by decide
theorem row_cert_39 : quickRow ⟨2,5242880,2,49150⟩ = true := by decide
theorem row_cert_40 : quickRow ⟨2,6291456,2,32766⟩ = true := by decide
theorem row_cert_41 : quickRow ⟨3,32767,3,24572⟩ = true := by decide
theorem row_cert_42 : quickRow ⟨3,32767,3,32732⟩ = true := by decide
theorem row_cert_43 : quickRow ⟨3,32767,3,48636⟩ = true := by decide
theorem row_cert_44 : quickRow ⟨3,32767,3,49116⟩ = true := by decide
theorem row_cert_45 : quickRow ⟨3,32767,3,55292⟩ = true := by decide
theorem row_cert_46 : quickRow ⟨3,32767,3,62972⟩ = true := by decide
theorem row_cert_47 : quickRow ⟨3,294911,2,56829⟩ = true := by decide
theorem row_cert_48 : quickRow ⟨3,360447,2,64989⟩ = true := by decide
theorem row_cert_49 : quickRow ⟨3,425983,2,57309⟩ = true := by decide
theorem row_cert_50 : quickRow ⟨3,1081343,1,47102⟩ = true := by decide
theorem row_cert_51 : quickRow ⟨3,4227071,1,16382⟩ = true := by decide
theorem row_cert_52 : quickRow ⟨4,1365,4,65021⟩ = true := by decide
theorem row_cert_53 : quickRow ⟨4,2184,4,64503⟩ = true := by decide
theorem row_cert_54 : quickRow ⟨4,131152,4,56831⟩ = true := by decide
theorem row_cert_55 : quickRow ⟨4,164113,4,64991⟩ = true := by decide
theorem row_cert_56 : quickRow ⟨4,327680,4,32759⟩ = true := by decide
theorem row_cert_57 : quickRow ⟨4,1573956,4,64255⟩ = true := by decide
theorem row_cert_58 : quickRow ⟨4,8552448,4,32511⟩ = true := by decide
theorem row_cert_59 : quickRow ⟨5,329045,0,32245⟩ = true := by decide
theorem row_cert_60 : quickRow ⟨8,1365,8,32766⟩ = true := by decide
theorem row_cert_61 : quickRow ⟨8,164113,8,64495⟩ = true := by decide
theorem row_cert_62 : quickRow ⟨8,1049856,8,16383⟩ = true := by decide
theorem row_cert_63 : quickRow ⟨8,1573956,8,30719⟩ = true := by decide
theorem quick_group_1 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (32+i.val))) = true := by
  fin_cases i
  · exact row_cert_32
  · exact row_cert_33
  · exact row_cert_34
  · exact row_cert_35
  · exact row_cert_36
  · exact row_cert_37
  · exact row_cert_38
  · exact row_cert_39
  · exact row_cert_40
  · exact row_cert_41
  · exact row_cert_42
  · exact row_cert_43
  · exact row_cert_44
  · exact row_cert_45
  · exact row_cert_46
  · exact row_cert_47
  · exact row_cert_48
  · exact row_cert_49
  · exact row_cert_50
  · exact row_cert_51
  · exact row_cert_52
  · exact row_cert_53
  · exact row_cert_54
  · exact row_cert_55
  · exact row_cert_56
  · exact row_cert_57
  · exact row_cert_58
  · exact row_cert_59
  · exact row_cert_60
  · exact row_cert_61
  · exact row_cert_62
  · exact row_cert_63
end G11GuardFront
