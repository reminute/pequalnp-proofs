import GuardQuickCaps

namespace G11GuardFront

theorem cap_verified (i j : Fin 574) : capOK (major i) (major j) = true := fast_caps i j

end G11GuardFront
