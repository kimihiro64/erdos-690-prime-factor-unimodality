import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanRemainder

/-! # Smooth subtraction and the actual Lehman remainder

Translation also works for complex integrands. Signed logarithmic weights
remain integrable. The unconditional error identity has no numerical
counting hypothesis; the quantitative estimate explicitly requires it.
Dropping the cutoff atom requires a separate zero-multiplicity proof.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

example (t H : ℝ) (f : ℝ → ℂ) (h : IntegrableOn (fun x => f (x + t)) (Ioi H)) :
    IntegrableOn f (Ioi (H + t)) :=
  (integrableOn_Ioi_comp_add_iff t H f).mp h

example : IntegrableOn (fun x : ℝ => x * (Real.log x - 100) *
    Real.reciprocalSquarePairSlope 1 x) (Ioi 2) := by
  convert Real.integrableOn_mul_log_sub_mul_reciprocalSquarePairSlope
    (t := 1) (H := 1) (by norm_num) (by norm_num) 100 using 1
  norm_num

example {t H : ℝ} (ht : 0 ≤ t) (hH : 0 < H) :
    Real.reciprocalSquarePairSlope t (t + H) ≤ (2 / H) * Real.reciprocalSquarePair t (t + H) :=
  Real.reciprocalSquarePairSlope_le ht hH le_rfl

example (t : ℝ) :
    Tendsto (fun x => xiZeroCountingMainTerm x * Real.reciprocalSquarePair t x) atTop (𝓝 0) :=
  tendsto_xiCountingMain_mul_pair t

example {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    xiHeightTail t H - xiLehmanMainIntegral t H =
      -xiZeroCountingRemainder (t + H) * Real.reciprocalSquarePair t (t + H) +
        (∫ x in Ioi (t + H), xiZeroCountingRemainder x * Real.reciprocalSquarePairSlope t x) +
        (xiOrdinateMultiplicity (t + H) : ℝ) * Real.reciprocalSquarePair t (t + H) :=
  xiHeightTail_sub_main_eq_error_add_boundary ht hH

example {t H : ℝ} (ht : 0 < t) (hH : 0 < H)
    (hR : ∀ x ∈ Ici (t + H), |xiZeroCountingRemainder x| ≤ 2 * Real.log x) :
    xiHeightTail t H ≤ xiLehmanMainIntegral t H + xiLehmanIntegralCorrection t H +
      (xiOrdinateMultiplicity (t + H) : ℝ) * Real.reciprocalSquarePair t (t + H) :=
  xiHeightTail_le_main_add_correction_of_counting_error ht hH hR

example {t H : ℝ} (ht : 0 < t) (hH : 0 < H)
    (hR : ∀ x ∈ Ici (t + H), |xiZeroCountingRemainder x| ≤ 2 * Real.log x)
    (hb : xiOrdinateMultiplicity (t + H) = 0) :
    xiHeightTail t H ≤ xiLehmanMainIntegral t H + xiLehmanIntegralCorrection t H := by
  simpa only [hb, Nat.cast_zero, zero_mul, add_zero] using
    xiHeightTail_le_main_add_correction_of_counting_error ht hH hR

end

end PrimeFactorUnimodality.Tests
