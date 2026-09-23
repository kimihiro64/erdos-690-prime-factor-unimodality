import PrimeFactorUnimodality.Helpers.Analytic.ZetaGroupedEvaluation

/-! # Shared exponential evaluation interfaces and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset

variable {ι κ : Type*} [DecidableEq κ]

example {d : ZetaGroupedBlock}
    (hd : d.Valid) {p : ZetaGroupedPoint} (hp : p.Valid d) :
    ‖zetaEulerApproxOrder d.cutoff ((1 / 2 : ℂ) + p.height d * I) d.order - p.value d‖ ≤
      p.roundingBudget d := by
  exact PrimeFactorUnimodality.ZetaGroupedPoint.Valid.norm_euler_sub_value_le hd hp

example {d : ZetaGroupedBlock}
    (hd : d.Valid) {p : ZetaGroupedPoint} (hp : p.Valid d) :
    ‖riemannZeta ((1 / 2 : ℂ) + p.height d * I) - p.value d‖ ≤ p.error d := by
  exact PrimeFactorUnimodality.ZetaGroupedPoint.Valid.norm_zeta_sub_value_le hd hp

example {d : ZetaGroupedBlock}
    (hd : d.Valid) {p : ZetaGroupedPoint} (hp : p.Valid d) : 0 ≤ p.error d := by
  exact PrimeFactorUnimodality.ZetaGroupedPoint.Valid.error_nonneg hd hp



end

end PrimeFactorUnimodality.Tests
