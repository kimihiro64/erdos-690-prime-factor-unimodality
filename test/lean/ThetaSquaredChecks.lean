import PrimeFactorUnimodality.Helpers.Analytic.ThetaSquaredChecks

/-! # Complete prime-block transitions and coverage regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open PrimeFactorUnimodality.ThetaSquaredCheckpoint

example {c : ℚ} {p q : ThetaSquaredCheckpoint}
    {points : List ThetaSquaredCheckpoint} (h : checkFrom c p q points = true) :
    Chain c p q (p :: points) := by
  exact PrimeFactorUnimodality.ThetaSquaredCheckpoint.chain_of_checkFrom h

example {c : ℚ} (hc : 0 ≤ c) {p q : ThetaSquaredCheckpoint}
    {points : List ThetaSquaredCheckpoint} (h : checkFrom c p q points = true)
    (hvalid : ∀ r ∈ p :: points, r.Valid) {x : ℝ}
    (hpx : (p.point : ℝ) ≤ x) (hxq : x ≤ q.point) :
    |Chebyshev.theta x - x| ≤ (c : ℝ) * x / Real.log x ^ 2 := by
  exact PrimeFactorUnimodality.ThetaSquaredCheckpoint.bound_of_checkFrom hc h hvalid hpx hxq

private def first : ThetaSquaredCheckpoint := ⟨2, 0, 1, 1⟩
private def last : ThetaSquaredCheckpoint := ⟨3, 0, 3, 2⟩

example : checkFrom 10 first last [last] = true := by decide +kernel

example : checkFrom 10 first last [] = false := by decide +kernel

example : checkFrom 10 first ⟨3, 0, 3, 3⟩ [last] = false := by decide +kernel

example : checkFrom 0 first last [last] = false := by decide +kernel

example : Chain 10 first last [first, last] :=
  chain_of_checkFrom (by decide +kernel)

end

end PrimeFactorUnimodality.Tests
