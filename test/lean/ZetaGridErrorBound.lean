import PrimeFactorUnimodality.Helpers.Analytic.ZetaGridErrorBound

/-! # Full grid-error interfaces and small rational boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open Fourier
open PrimeFactorUnimodality

example {d : ZetaGridBlock} (hd : d.Valid)
    (p : ZetaGridPoint) (hp : |p.coordinate d| ≤ 1) :
    p.error d ≤ zetaEulerError d.shared.cutoff ((1 / 2 : ℂ) + p.height d * I) d.shared.order +
      d.shared.cutoff * ((1 / 2 : ℝ) ^ d.shared.degree * Real.exp (1 / 2)) +
      (∑ b ∈ d.shared.groups, ∑ j ∈ range d.shared.degree, d.shared.coefficientError b j) +
      p.correctionError + ∑ j ∈ range d.shared.degree, (d.trace j).error := by
  exact PrimeFactorUnimodality.ZetaGridPoint.error_le_shared hd p hp



end

end PrimeFactorUnimodality.Tests
