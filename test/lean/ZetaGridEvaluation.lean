import Mathlib.Tactic.FinCases
import PrimeFactorUnimodality.Helpers.Analytic.ZetaGridEvaluation

/-! # Radix/grid interfaces, collisions and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Fourier ZMod



example {d : ZetaGridBlock} (hd : d.Valid)
    (p : ZetaGridPoint) :
    ‖(p.asGrouped d).value d.shared - p.value d‖ ≤ p.transformError d := by
  exact PrimeFactorUnimodality.ZetaGridBlock.Valid.norm_grouped_sub_value_le hd p

example {d : ZetaGridBlock} (hd : d.Valid)
    {p : ZetaGridPoint} (hp : p.Valid d) :
    ‖riemannZeta ((1 / 2 : ℂ) + p.height d * I) - p.value d‖ ≤ p.error d := by
  exact PrimeFactorUnimodality.ZetaGridPoint.Valid.norm_zeta_sub_value_le hd hp

example {d : ZetaGridBlock} (hd : d.Valid)
    {p : ZetaGridPoint} (hp : p.Valid d) : 0 ≤ p.error d := by
  exact PrimeFactorUnimodality.ZetaGridPoint.Valid.error_nonneg hd hp

example {d : ZetaGridBlock} (p : ZetaGridPoint) {h : ℝ}
    (hr : d.shared.radius = h * (2 ^ d.levels) / (2 * Real.pi)) :
    p.height d = d.shared.base + h * p.index := by
  exact PrimeFactorUnimodality.ZetaGridPoint.height_of_radius p hr

example {d : ZetaGridBlock} (hr : d.shared.radius = (2 ^ d.levels) / (2 * Real.pi))
    (c : ℂ) (e : ℝ) : (ZetaGridPoint.mk (-1) c e).height d = d.shared.base - 1 := by
  have h := ZetaGridPoint.height_of_radius (ZetaGridPoint.mk (-1) c e) (h := 1) (by simpa using hr)
  simpa [sub_eq_add_neg] using h

end

end PrimeFactorUnimodality.Tests
