import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.DusartCheckpointAnchors

/-! # Exact interfaces and real-interval checkpoint regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open PrimeFactorUnimodality.ThetaSquaredCheckpoint

example {p : ThetaSquaredCheckpoint} (hp : p.Valid)
    {L : ℚ} (hL0 : 0 ≤ L) (hL : (L : ℝ) ≤ Real.log p.point)
    {k : ℕ} (hk : k ≤ Nat.primeCounting p.point)
    (hmargin : p.upper * p.logUpper ^ 2 + (p.point : ℚ) * p.logUpper +
      (1 / 5 : ℚ) * p.point ≤ (k : ℚ) * L ^ 3) :
    Chebyshev.theta p.point * Real.log p.point ^ 2 +
      (p.point : ℝ) * Real.log p.point + (1 / 5 : ℝ) * p.point ≤
        (Nat.primeCounting p.point : ℝ) * Real.log p.point ^ 3 := by
  exact PrimeFactorUnimodality.ThetaSquaredCheckpoint.lower_anchor hp hL0 hL hk hmargin

example {p : ThetaSquaredCheckpoint} (hp : p.Valid)
    {L : ℚ} (hL0 : 0 ≤ L)
    (hL : (L : ℝ) ≤ Real.log p.point) {k : ℕ} (hk : Nat.primeCounting p.point ≤ k)
    (hmargin : (k : ℚ) * p.logUpper ^ 3 ≤ p.lower * L ^ 2 +
      (6381 / 5000 : ℚ) * p.point * L - (1 / 5 : ℚ) * p.point) :
    (Nat.primeCounting p.point : ℝ) * Real.log p.point ^ 3 ≤
      Chebyshev.theta p.point * Real.log p.point ^ 2 +
        (6381 / 5000 : ℝ) * p.point * Real.log p.point - (1 / 5 : ℝ) * p.point := by
  exact PrimeFactorUnimodality.ThetaSquaredCheckpoint.upper_anchor hp hL0 hL hk hmargin



end

end PrimeFactorUnimodality.Tests
