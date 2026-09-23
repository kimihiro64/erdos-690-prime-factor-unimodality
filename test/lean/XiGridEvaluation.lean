import Mathlib.Tactic.FinCases
import PrimeFactorUnimodality.Helpers.Analytic.XiGridEvaluation

/-! # Radix/grid interfaces, collisions and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Fourier ZMod



example {d : ZetaGridBlock} (hd : d.Valid)
    {p : ZetaGridPoint} (hp : p.Valid d) {θ δ : ℝ}
    (hθ : |turingStirlingPhase (p.height d) - θ| ≤ δ) :
    |xiNormalizedValue (p.height d) - p.xiApprox d θ| ≤ p.xiError d δ := by
  exact PrimeFactorUnimodality.ZetaGridPoint.Valid.abs_xi_sub_approx_le hd hp hθ

example {row : XiSignRow} (hwidth : row.lower < row.upper)
    {d e : ZetaGridBlock} (hd : d.Valid) (he : e.Valid)
    {p q : ZetaGridPoint} (hp : p.Valid d) (hq : q.Valid e)
    (hlower : p.height d = (row.lower : ℝ)) (hupper : q.height e = (row.upper : ℝ))
    {θ φ δ ε : ℝ} (hθ : |turingStirlingPhase (p.height d) - θ| ≤ δ)
    (hφ : |turingStirlingPhase (q.height e) - φ| ≤ ε)
    (hmargin : (p.xiError d δ < p.xiApprox d θ ∧ q.xiApprox e φ < -q.xiError e ε) ∨
      (p.xiApprox d θ < -p.xiError d δ ∧ q.xiError e ε < q.xiApprox e φ)) : row.Valid := by
  exact PrimeFactorUnimodality.XiSignRow.valid_of_grid_endpoints hwidth hd he hp hq hlower hupper hθ hφ hmargin



end

end PrimeFactorUnimodality.Tests
