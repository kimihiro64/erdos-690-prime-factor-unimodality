import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.ThetaSquaredCheckpoints

/-! # Exact interfaces and real-interval checkpoint regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open PrimeFactorUnimodality.ThetaSquaredCheckpoint

example {c : ℚ} (hc : 0 ≤ c) {p q : ThetaSquaredCheckpoint}
    (hp : p.Valid) (hq : q.Valid) (hstep : Step c p q) {x : ℝ}
    (hpx : (p.point : ℝ) ≤ x) (hxq : x ≤ q.point) :
    |Chebyshev.theta x - x| ≤ (c : ℝ) * x / Real.log x ^ 2 := by
  exact PrimeFactorUnimodality.ThetaSquaredCheckpoint.Step.bound hc hp hq hstep hpx hxq

example : Step 6 ⟨2, 0, 2, 2⟩ ⟨3, 0, 3, 2⟩ := by norm_num [Step]

example : ¬Step 6 ⟨3, 0, 3, 2⟩ ⟨2, 0, 2, 2⟩ := by norm_num [Step]

example : ¬Step (-1) ⟨2, 0, 2, 2⟩ ⟨2, 0, 2, 2⟩ := by norm_num [Step]

example {c : ℚ} (hc : 0 ≤ c) {p : ThetaSquaredCheckpoint}
    (hp : p.Valid) (h : Step c p p) :
    |Chebyshev.theta p.point - p.point| ≤ (c : ℝ) * p.point / Real.log p.point ^ 2 :=
  h.bound hc hp hp le_rfl le_rfl

end

end PrimeFactorUnimodality.Tests
