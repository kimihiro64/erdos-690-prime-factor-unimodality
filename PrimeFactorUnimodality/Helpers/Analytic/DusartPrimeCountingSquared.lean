import PrimeFactorUnimodality.Helpers.Analytic.DusartTwoTermComparison
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.ThetaLogSquaredError

/-! # Direct prime-counting assembly from the log-square theta estimate

Use the exact anchored Abel comparison and the requested two-term models.
Coefficient one fifth and logarithmic starting height ten discharge the
derivative margins. The two anchor inequalities and finite prime-counting
prefix remain separate explicit inputs, with no integral remainder input.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- A single log-square theta error supplies both requested unbounded prime-counting estimates. -/
theorem hasDusartRealPrimeCountingBoundsAbove_of_thetaLogSquared {X : ℝ}
    (hX : 2 ≤ X) (hlogX : 10 ≤ Real.log X)
    (error : HasThetaLogSquaredError (1 / 5) X)
    (lowerAnchor : dusartPiLower X ≤ dusartJ 2 (-(1 / 5)) X X)
    (upperAnchor : dusartJ 2 (1 / 5) X X ≤ dusartPiUpper X) :
    HasDusartRealPrimeCountingBoundsAbove X := by
  have hX1 : 1 < X := by linarith
  have hmargin : (6381 / 2500 : ℝ) + 1 / 5 ≤ (1381 / 5000 : ℝ) * Real.log X := by
    linarith
  constructor
  · intro x hx
    have hj := (dusartJ_sandwich (k := 2) (η := 1 / 5) hX hx
      (fun t ht => error t ht.1)).1
    exact (dusartPiLower_le_dusartJ_two hX1 hx (by norm_num) (by norm_num) lowerAnchor).trans hj
  · intro x hx
    have hj := (dusartJ_sandwich (k := 2) (η := 1 / 5) hX hx
      (fun t ht => error t ht.1)).2
    exact hj.trans (dusartJ_two_le_dusartPiUpper hX1 hx (by norm_num) hmargin upperAnchor)

/-- The exact global natural-number bounds follow after supplying their bounded prefix. -/
theorem hasDusartPrimeCountingBounds_of_thetaLogSquared {X : ℝ}
    (hX : 2 ≤ X) (hlogX : 10 ≤ Real.log X)
    (finite : HasDusartRealPrimeCountingBoundsBelow X)
    (error : HasThetaLogSquaredError (1 / 5) X)
    (lowerAnchor : dusartPiLower X ≤ dusartJ 2 (-(1 / 5)) X X)
    (upperAnchor : dusartJ 2 (1 / 5) X X ≤ dusartPiUpper X) :
    HasDusartPrimeCountingBounds :=
  hasDusartPrimeCountingBounds_of_real
    (hasDusartRealPrimeCountingBounds_of_below_and_above finite
      (hasDusartRealPrimeCountingBoundsAbove_of_thetaLogSquared hX hlogX error
        lowerAnchor upperAnchor))

end

end PrimeFactorUnimodality
