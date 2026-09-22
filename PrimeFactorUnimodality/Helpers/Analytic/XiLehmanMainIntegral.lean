import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogReciprocalSquarePair

/-! # Exact main integral for the positive-height zero tail

Evaluate the main integral in Mossinghoff--Trudgian, Section 4, and combine
it with the already-proved elementary correction. This removes numerical
integration from this expression. The zero-counting inequality relating
the expression to the actual zero sum is a separate obligation.
Source: https://arxiv.org/pdf/1410.3926
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Real Set

/-- The main term after translating the positive-ordinate cutoff by `t`. -/
def xiLehmanMainIntegral (t H : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ x in Ioi H,
    Real.log ((x + t) / (2 * π)) * Real.reciprocalSquarePair t (x + t)

/-- The main term is an actual integrable improper integral for every positive cutoff. -/
theorem integrableOn_xiLehmanMainIntegrand {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    IntegrableOn (fun x =>
      Real.log ((x + t) / (2 * π)) * Real.reciprocalSquarePair t (x + t)) (Ioi H) :=
  Real.integrableOn_log_div_reciprocalSquarePair_add ht hH (by positivity)

/-- Closed form with no quadrature or finite certificate. -/
theorem xiLehmanMainIntegral_eq {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    xiLehmanMainIntegral t H =
      (1 / (2 * π)) * (Real.log ((H + t) / (2 * π)) * (1 / H + 1 / (H + 2 * t)) +
        Real.log ((H + 2 * t) / H) / t) := by
  unfold xiLehmanMainIntegral
  rw [Real.integral_log_div_reciprocalSquarePair_add ht hH (by positivity)]

/-- The combined integral expression has a fully elementary upper bound. -/
theorem xiLehmanMainIntegral_add_correction_le {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    xiLehmanMainIntegral t H + xiLehmanIntegralCorrection t H ≤
      (1 / (2 * π)) * (Real.log ((H + t) / (2 * π)) * (1 / H + 1 / (H + 2 * t)) +
        Real.log ((H + 2 * t) / H) / t) +
      4 * Real.log (t + H) * (1 / H ^ 2 + 1 / (H + 2 * t) ^ 2) + 4 / (t * H) := by
  rw [xiLehmanMainIntegral_eq ht hH, add_assoc]
  exact add_le_add le_rfl (xiLehmanIntegralCorrection_le ht hH)

end

end PrimeFactorUnimodality
