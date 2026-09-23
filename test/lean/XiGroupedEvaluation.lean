import PrimeFactorUnimodality.Helpers.Analytic.XiGroupedEvaluation

/-! # Shared exponential evaluation interfaces and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset

variable {ι κ : Type*} [DecidableEq κ]

example {d : ZetaGroupedBlock}
    (hd : d.Valid) {p : ZetaGroupedPoint} (hp : p.Valid d) {θ δ : ℝ}
    (hθ : |turingStirlingPhase (p.height d) - θ| ≤ δ) :
    |xiNormalizedValue (p.height d) - p.xiApprox d θ| ≤ p.xiError d δ := by
  exact PrimeFactorUnimodality.ZetaGroupedPoint.Valid.abs_xi_sub_approx_le hd hp hθ

example {d : ZetaGroupedBlock}
    (hd : d.Valid) {p : ZetaGroupedPoint} (hp : p.Valid d) {θ δ : ℝ}
    (hθ : |turingStirlingPhase (p.height d) - θ| ≤ δ)
    (hmargin : p.xiError d δ < p.xiApprox d θ) : 0 < xiCriticalLineValue (p.height d) := by
  exact PrimeFactorUnimodality.ZetaGroupedPoint.Valid.xi_pos hd hp hθ hmargin

example {d : ZetaGroupedBlock}
    (hd : d.Valid) {p : ZetaGroupedPoint} (hp : p.Valid d) {θ δ : ℝ}
    (hθ : |turingStirlingPhase (p.height d) - θ| ≤ δ)
    (hmargin : p.xiApprox d θ < -p.xiError d δ) : xiCriticalLineValue (p.height d) < 0 := by
  exact PrimeFactorUnimodality.ZetaGroupedPoint.Valid.xi_neg hd hp hθ hmargin

example {row : XiSignRow} (hwidth : row.lower < row.upper)
    {d e : ZetaGroupedBlock} (hd : d.Valid) (he : e.Valid)
    {p q : ZetaGroupedPoint} (hp : p.Valid d) (hq : q.Valid e)
    (hlower : p.height d = (row.lower : ℝ)) (hupper : q.height e = (row.upper : ℝ))
    {θ φ δ ε : ℝ} (hθ : |turingStirlingPhase (p.height d) - θ| ≤ δ)
    (hφ : |turingStirlingPhase (q.height e) - φ| ≤ ε)
    (hmargin : (p.xiError d δ < p.xiApprox d θ ∧ q.xiApprox e φ < -q.xiError e ε) ∨
      (p.xiApprox d θ < -p.xiError d δ ∧ q.xiError e ε < q.xiApprox e φ)) : row.Valid := by
  exact PrimeFactorUnimodality.XiSignRow.valid_of_grouped_endpoints hwidth hd he hp hq hlower hupper hθ hφ hmargin



end

end PrimeFactorUnimodality.Tests
