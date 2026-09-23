import Mathlib.Tactic.FinCases
import PrimeFactorUnimodality.Helpers.Analytic.ZetaGridData

/-! # Radix/grid interfaces, collisions and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Fourier ZMod



example {p : ZetaGridPoint} {d : ZetaGridBlock}
    (hp : p.Valid d) : (p.asGrouped d).Valid d.shared := by
  exact PrimeFactorUnimodality.ZetaGridPoint.Valid.asGrouped hp

example (d : ZetaGridBlock) (c : ℂ) (e : ℝ) :
    (ZetaGridPoint.mk 0 c e).coordinate d = 0 := by simp [ZetaGridPoint.coordinate]

example (d : ZetaGridBlock) (c : ℂ) (e : ℝ) :
    (ZetaGridPoint.mk 0 c e).height d = d.shared.base := by
  simp [ZetaGridPoint.height, ZetaGridPoint.coordinate]

end

end PrimeFactorUnimodality.Tests
