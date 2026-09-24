import PrimeFactorUnimodality.Helpers.Analytic.DusartSquaredAtPublishedCutoff
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.PrimeCountingLogBounds

set_option autoImplicit false

/-! # The published Abel anchors from the same theta error

At 3,594,641 the log-square theta estimate already leaves sufficient margin
for both Abel anchors. An exact prime count and elementary logarithm bounds
therefore replace a separate theta-product certificate at this boundary.
This is a consequence of the theta estimate, not a proof of that estimate.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Coarse logarithm bounds obtained from two small smooth integers. -/
theorem dusart_published_log_bounds :
    (377 / 25 : Real) ≤ Real.log 3594641 ∧ Real.log 3594641 ≤ (151 / 10 : Real) := by
  have lower := log_nat_lower_of_smooth_power
    (n := 3594641) (s := 1) (a := 2) (b := 11) (c := 1) (by decide) (by decide)
  have upper := log_nat_upper_of_smooth_power
    (n := 3594641) (s := 1) (a := 7) (b := 2) (c := 5)
    (by decide) (by decide) (by decide)
  norm_num at lower upper
  constructor <;> linarith

/-- The exact count and the theta bound at the cutoff imply both required
anchors; no separate enclosure of the prime logarithm sum is necessary. -/
theorem dusart_published_anchors_of_count
    (count : Nat.primeCounting 3594641 = 256357)
    (error : |Chebyshev.theta 3594641 - 3594641| ≤
      (1 / 5 : Real) * 3594641 / Real.log 3594641 ^ 2) :
    (Chebyshev.theta 3594641 * Real.log 3594641 ^ 2 +
      3594641 * Real.log 3594641 + (1 / 5 : Real) * 3594641 ≤
        (Nat.primeCounting 3594641 : Real) * Real.log 3594641 ^ 3) ∧
    ((Nat.primeCounting 3594641 : Real) * Real.log 3594641 ^ 3 ≤
      Chebyshev.theta 3594641 * Real.log 3594641 ^ 2 +
        (6381 / 5000 : Real) * 3594641 * Real.log 3594641 -
          (1 / 5 : Real) * 3594641) := by
  obtain ⟨logLower, logUpper⟩ := dusart_published_log_bounds
  have logPos : (0 : Real) < Real.log 3594641 := by linarith
  have scaled := (le_div_iff₀ (sq_pos_of_pos logPos)).mp error
  have scaledAbs : |(Chebyshev.theta 3594641 - 3594641) * Real.log 3594641 ^ 2| ≤
      (1 / 5 : Real) * 3594641 := by
    simpa only [abs_mul, abs_of_nonneg (sq_nonneg (Real.log 3594641))] using scaled
  obtain ⟨thetaLower, thetaUpper⟩ := abs_le.mp scaledAbs
  have squareLower := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 377 / 25) logLower 2
  have squareUpper := pow_le_pow_left₀ logPos.le logUpper 2
  have cubeLower := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 377 / 25) logLower 3
  have cubeUpper := pow_le_pow_left₀ logPos.le logUpper 3
  rw [count]
  norm_num only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 3594641 * Real.log 3594641 ^ 2 + 3594641 * Real.log 3594641 +
          (2 / 5 : Real) * 3594641 := by nlinarith only [thetaUpper]
      _ ≤ 3594641 * (151 / 10 : Real) ^ 2 + 3594641 * (151 / 10 : Real) +
          (2 / 5 : Real) * 3594641 := by nlinarith only [squareUpper, logUpper]
      _ ≤ 256357 * (377 / 25 : Real) ^ 3 := by norm_num
      _ ≤ _ := by nlinarith only [cubeLower]
  · calc
      _ ≤ 256357 * (151 / 10 : Real) ^ 3 := by nlinarith only [cubeUpper]
      _ ≤ 3594641 * (377 / 25 : Real) ^ 2 +
          (6381 / 5000 : Real) * 3594641 * (377 / 25 : Real) -
            (2 / 5 : Real) * 3594641 := by norm_num
      _ ≤ 3594641 * Real.log 3594641 ^ 2 +
          (6381 / 5000 : Real) * 3594641 * Real.log 3594641 -
            (2 / 5 : Real) * 3594641 := by nlinarith only [squareLower, logLower]
      _ ≤ _ := by nlinarith only [thetaLower]

/-- Once the endpoint count is supplied, the theta estimate also discharges
both Abel anchors in the global prime-counting provider. -/
theorem hasDusartPrimeCountingBounds_of_published_logSquared_count
    (count : Nat.primeCounting 3594641 = 256357)
    (finite : HasDusartRealPrimeCountingBoundsBelow 3594641)
    (error : HasThetaLogSquaredError (1 / 5) 3594641) : HasDusartPrimeCountingBounds := by
  have anchors := dusart_published_anchors_of_count count (error _ le_rfl)
  exact hasDusartPrimeCountingBounds_of_published_logSquared
    finite error anchors.1 anchors.2

end

end PrimeFactorUnimodality
