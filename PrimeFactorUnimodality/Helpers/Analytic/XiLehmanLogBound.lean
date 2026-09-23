import PrimeFactorUnimodality.Helpers.Analytic.BacklundCountingHigh
import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanRemainder

/-! # A Lehman tail bound retaining the additive counting error

Use the proved `log(T)+17` discrepancy directly instead of absorbing seventeen
into another logarithm. The closed tail includes every cutoff multiplicity:
its boundary atom combines with the closed count to give the strict count.
The resulting bound holds for `t+H>10`, without a billion-height restriction.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real Set MeasureTheory

/-- Elementary evaluation of the main integral and the full logarithmic error. -/
def xiLehmanLogBound (t H : ℝ) : ℝ :=
  (1 / (2 * π)) * (Real.log ((H + t) / (2 * π)) * (1 / H + 1 / (H + 2 * t)) +
    Real.log ((H + 2 * t) / H) / t) +
  (2 * Real.log (t + H) + 34) * (1 / H ^ 2 + 1 / (H + 2 * t) ^ 2) + 2 / (t * H)

/-- The exact logarithmic-envelope correction controls the closed tail at moderate height. -/
theorem xiHeightTail_le_main_add_log_error {t H : ℝ}
    (ht : 0 < t) (hH : 0 < H) (hA : 10 < t + H) :
    xiHeightTail t H ≤ xiLehmanMainIntegral t H +
      2 * (Real.log (t + H) + 17) * Real.reciprocalSquarePair t (t + H) +
        ∫ x in Ioi (t + H), Real.reciprocalSquarePair t x / x := by
  have hRi := integrableOn_xiCountingRemainder_mul_slope ht hH
  have hLi : IntegrableOn
      (fun x => (Real.log x + 17) * Real.reciprocalSquarePairSlope t x)
      (Ioi (t + H)) := by
    simpa only [sub_neg_eq_add] using
      Real.integrableOn_log_sub_mul_reciprocalSquarePairSlope ht hH (-17)
  have hI : (∫ x in Ioi (t + H),
      xiZeroCountingRemainder x * Real.reciprocalSquarePairSlope t x) ≤
        ∫ x in Ioi (t + H), (Real.log x + 17) * Real.reciprocalSquarePairSlope t x := by
    apply integral_mono_ae hRi hLi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : t + H < x := hx
    exact mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (abs_xiZeroCountingRemainder_le_log_add (by linarith)))
      (Real.reciprocalSquarePairSlope_nonneg ht.le (by linarith))
  have hB := mul_le_mul_of_nonneg_right
    ((neg_le_abs ((xiStrictZeroCount (t + H) : ℝ) - xiZeroCountingMainTerm (t + H))).trans
      (abs_xiStrictZeroCount_sub_mainTerm_le_log_add hA))
    (Real.reciprocalSquarePair_pos ht.le (by linarith : t < t + H)).le
  have hc : (xiZeroCount (t + H) : ℝ) = (xiStrictZeroCount (t + H) : ℝ) +
      (xiOrdinateMultiplicity (t + H) : ℝ) := by
    exact_mod_cast xiZeroCount_eq_strict_add_multiplicity (by linarith : 0 < t + H)
  have he : xiHeightTail t H - xiLehmanMainIntegral t H =
      -((xiStrictZeroCount (t + H) : ℝ) - xiZeroCountingMainTerm (t + H)) *
        Real.reciprocalSquarePair t (t + H) +
          ∫ x in Ioi (t + H), xiZeroCountingRemainder x * Real.reciprocalSquarePairSlope t x := by
    rw [xiHeightTail_sub_main_eq_error_add_boundary ht hH]
    conv_lhs => lhs; lhs; rw [xiZeroCountingRemainder, hc]
    ring
  have hJ := Real.integral_log_sub_mul_reciprocalSquarePairSlope ht hH (-17)
  simp only [sub_neg_eq_add] at hJ
  rw [hJ] at hI
  linarith only [he, hB, hI]

/-- No improper integrals or numerical zero-location premises remain in the bound. -/
theorem xiHeightTail_le_logBound {t H : ℝ}
    (ht : 0 < t) (hH : 0 < H) (hA : 10 < t + H) :
    xiHeightTail t H ≤ xiLehmanLogBound t H := by
  have h := xiHeightTail_le_main_add_log_error ht hH hA
  rw [xiLehmanMainIntegral_eq ht hH, show t + H = H + t by ring,
    ← integral_Ioi_comp_add t H (fun x => Real.reciprocalSquarePair t x / x),
    Real.reciprocalSquarePair_add] at h
  have hI := Real.integral_reciprocalSquarePair_div_add_le ht hH
  dsimp only [xiLehmanLogBound]
  rw [add_comm t H]
  nlinarith only [h, hI]

end

end PrimeFactorUnimodality
