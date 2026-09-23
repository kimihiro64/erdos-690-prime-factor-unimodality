import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxOscillation
import PrimeFactorUnimodality.Helpers.Analytic.XiLowConjugatePartition
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageConjugation

/-! # Conjugate pairing of the actual box phase sum

Only positive-ordinate data need be stored. The negative contributions are
their exact conjugates, including the centered coefficient phase. Pairing
preserves cancellation and reduces the full sum to twice a real part.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Finset intervalIntegral
open scoped ComplexConjugate

/-- Fixed box coefficients respect the actual divisor-label conjugation. -/
theorem dusartBoxZeroCoefficient_conjugation (m : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (u : ℝ) (p : RiemannXiDivisorZeroIndex) :
    dusartBoxZeroCoefficient m s u (riemannXiDivisorConjugation p) =
      conj (dusartBoxZeroCoefficient m s u p) := by
  unfold dusartBoxZeroCoefficient
  simp only [riemannXiDivisorZeroValue_conjugation, conj_im]
  rw [iteratedBoxAverageComplex_cpow_div_conj hs zero_lt_one, map_mul, ← exp_conj]
  congr 1
  congr 1
  simp only [mul_neg, ofReal_neg, map_mul, conj_I, conj_ofReal, neg_mul]

/-- The entire oscillatory contribution of a conjugate label is conjugated exactly. -/
theorem dusartBoxPhaseAtom_conjugation (m : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (u v : ℝ) (p : RiemannXiDivisorZeroIndex) :
    dusartBoxZeroCoefficient m s u (riemannXiDivisorConjugation p) *
        exp (I * ((v * (riemannXiDivisorZeroValue (riemannXiDivisorConjugation p)).im : ℝ) : ℂ)) =
      conj (dusartBoxZeroCoefficient m s u p *
        exp (I * ((v * (riemannXiDivisorZeroValue p).im : ℝ) : ℂ))) := by
  rw [dusartBoxZeroCoefficient_conjugation m hs, riemannXiDivisorZeroValue_conjugation,
    conj_im, map_mul, ← exp_conj]
  congr 1
  congr 1
  simp only [mul_neg, ofReal_neg, map_mul, conj_I, conj_ofReal, neg_mul]

/-- Positive-ordinate data determine the complete low sum, including multiplicities. -/
theorem dusartBoxLowPhaseSum_eq_twice_re (m : ℕ) {s : ℝ} (hs : 0 ≤ s) (u T v : ℝ) :
    dusartBoxLowPhaseSum m s u T v =
      ((2 * (∑ p ∈ xiStrictPositiveHeightIndices T, dusartBoxZeroCoefficient m s u p *
        exp (I * ((v * (riemannXiDivisorZeroValue p).im : ℝ) : ℂ))).re : ℝ) : ℂ) := by
  unfold dusartBoxLowPhaseSum
  rw [sum_xiLow_eq_positive_conjugate]
  simp_rw [dusartBoxPhaseAtom_conjugation m hs]
  rw [sum_add_distrib, ← map_sum]
  apply Complex.ext
  · simp only [add_re, conj_re, ofReal_re]
    ring
  · simp only [add_im, conj_im, ofReal_im, add_neg_cancel]

/-- The full low phase sum is real; its norm is twice the absolute positive-sum real part. -/
theorem norm_dusartBoxLowPhaseSum_eq (m : ℕ) {s : ℝ} (hs : 0 ≤ s) (u T v : ℝ) :
    ‖dusartBoxLowPhaseSum m s u T v‖ =
      2 * |(∑ p ∈ xiStrictPositiveHeightIndices T, dusartBoxZeroCoefficient m s u p *
        exp (I * ((v * (riemannXiDivisorZeroValue p).im : ℝ) : ℂ))).re| := by
  rw [dusartBoxLowPhaseSum_eq_twice_re m hs, norm_real, Real.norm_eq_abs, abs_mul]
  norm_num

end

end PrimeFactorUnimodality
