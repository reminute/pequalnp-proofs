import GuardCapLookup

namespace G11GuardFront
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
theorem row_cert_64 : quickRow ⟨8,6291456,8,65019⟩ = true := by decide
theorem row_cert_65 : quickRow ⟨8,8552448,8,62463⟩ = true := by decide
theorem row_cert_66 : quickRow ⟨8,9961472,8,64767⟩ = true := by decide
theorem row_cert_67 : quickRow ⟨10,6292821,0,32250⟩ = true := by decide
theorem row_cert_68 : quickRow ⟨12,10126677,12,32243⟩ = true := by decide
theorem row_cert_69 : quickRow ⟨12,10126677,12,63987⟩ = true := by decide
theorem row_cert_70 : quickRow ⟨12,10128861,8,64247⟩ = true := by decide
theorem row_cert_71 : quickRow ⟨12,10454357,8,32503⟩ = true := by decide
theorem row_cert_72 : quickRow ⟨12,16418133,4,64763⟩ = true := by decide
theorem row_cert_73 : quickRow ⟨16,192,16,57311⟩ = true := by decide
theorem row_cert_74 : quickRow ⟨16,2184,16,64991⟩ = true := by decide
theorem row_cert_75 : quickRow ⟨16,3276,16,65501⟩ = true := by decide
theorem row_cert_76 : quickRow ⟨16,17152,16,47103⟩ = true := by decide
theorem row_cert_77 : quickRow ⟨16,28672,16,30719⟩ = true := by decide
theorem row_cert_78 : quickRow ⟨16,29491,16,63486⟩ = true := by decide
theorem row_cert_79 : quickRow ⟨16,164113,16,64503⟩ = true := by decide
theorem row_cert_80 : quickRow ⟨16,328226,16,64255⟩ = true := by decide
theorem row_cert_81 : quickRow ⟨16,491520,16,31743⟩ = true := by decide
theorem row_cert_82 : quickRow ⟨17,494796,0,31709⟩ = true := by decide
theorem row_cert_83 : quickRow ⟨19,32767,3,63452⟩ = true := by decide
theorem row_cert_84 : quickRow ⟨20,166297,0,63959⟩ = true := by decide
theorem row_cert_85 : quickRow ⟨21,495069,0,31189⟩ = true := by decide
theorem row_cert_86 : quickRow ⟨32,17152,32,53247⟩ = true := by decide
theorem row_cert_87 : quickRow ⟨32,28672,32,64767⟩ = true := by decide
theorem row_cert_88 : quickRow ⟨32,102403,32,57279⟩ = true := by decide
theorem row_cert_89 : quickRow ⟨32,164113,32,65019⟩ = true := by decide
theorem row_cert_90 : quickRow ⟨32,491520,32,65532⟩ = true := by decide
theorem row_cert_91 : quickRow ⟨32,6291456,32,64495⟩ = true := by decide
theorem row_cert_92 : quickRow ⟨32,8388608,32,63471⟩ = true := by decide
theorem row_cert_93 : quickRow ⟨35,491520,35,65500⟩ = true := by decide
theorem row_cert_94 : quickRow ⟨40,6455569,0,63979⟩ = true := by decide
theorem row_cert_95 : quickRow ⟨48,521011,48,55247⟩ = true := by decide
theorem quick_group_2 (i : Fin 32) :
    quickRow (major (Fin.ofNat 574 (64+i.val))) = true := by
  fin_cases i
  · exact row_cert_64
  · exact row_cert_65
  · exact row_cert_66
  · exact row_cert_67
  · exact row_cert_68
  · exact row_cert_69
  · exact row_cert_70
  · exact row_cert_71
  · exact row_cert_72
  · exact row_cert_73
  · exact row_cert_74
  · exact row_cert_75
  · exact row_cert_76
  · exact row_cert_77
  · exact row_cert_78
  · exact row_cert_79
  · exact row_cert_80
  · exact row_cert_81
  · exact row_cert_82
  · exact row_cert_83
  · exact row_cert_84
  · exact row_cert_85
  · exact row_cert_86
  · exact row_cert_87
  · exact row_cert_88
  · exact row_cert_89
  · exact row_cert_90
  · exact row_cert_91
  · exact row_cert_92
  · exact row_cert_93
  · exact row_cert_94
  · exact row_cert_95
end G11GuardFront
