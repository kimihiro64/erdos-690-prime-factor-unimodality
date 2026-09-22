import PrimeFactorUnimodality.Helpers.Analytic.XiHeightTailEndpoint

/-! # The elementary integral in the Lehman zero-tail correction

Evaluate the easy part of the correction in Mossinghoff--Trudgian,
Section 4: after translation its divided-kernel integral is bounded by
`4/(t H)`. The positive kernel has its continuity, positivity, and
monotonicity proved in the candidate layer. The zero-counting/Lehman
theorem giving this correction for a zero sum is still a separate proof.
Source: https://arxiv.org/pdf/1410.3926
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Real Set

/-- The translated error expression prior to bounding its integral. -/
def xiLehmanIntegralCorrection (t H : ℝ) : ℝ :=
  4 * Real.log (t + H) * Real.reciprocalSquarePair t (H + t) +
    2 * ∫ x in Ioi H, Real.reciprocalSquarePair t (x + t) / (x + t)

/-- The exact elementary correction bound used at every positive harmonic height. -/
theorem xiLehmanIntegralCorrection_le {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    xiLehmanIntegralCorrection t H ≤
      4 * Real.log (t + H) * (1 / H ^ 2 + 1 / (H + 2 * t) ^ 2) + 4 / (t * H) := by
  unfold xiLehmanIntegralCorrection
  rw [Real.reciprocalSquarePair_add]
  have h := mul_le_mul_of_nonneg_left
    (Real.integral_reciprocalSquarePair_div_add_le ht hH) (by norm_num : (0 : ℝ) ≤ 2)
  simp only [div_eq_mul_inv] at h ⊢
  linarith

/-- Zero boundary multiplicity is the precise condition for dropping the cutoff correction. -/
theorem xiHeightTail_eq_strict_of_no_boundary {H : ℝ} (hH : 0 < H) (t : ℝ)
    (hboundary : xiOrdinateMultiplicity (|t| + H) = 0) :
    xiHeightTail t H =
      ∑' p : {p : RiemannXiDivisorZeroIndex // |t| + H < (riemannXiDivisorZeroValue p).im},
        Real.reciprocalSquarePair t (riemannXiDivisorZeroValue p.1).im := by
  rw [xiHeightTail_eq_strict_positive_add_boundary hH, hboundary, Nat.cast_zero, zero_mul, add_zero]

end

end PrimeFactorUnimodality
