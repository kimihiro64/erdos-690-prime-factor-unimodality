import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiDivisorConjugation
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiHadamardConstant
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.LogStep.PairBound

/-! # The full xi logarithmic-step budget

Same-height reflection pairs the actual multiplicity labels. The uniform
kernel bound and the existing absolutely convergent resolvent series give
a complete logarithmic-step sum, controlled by the xi logarithmic derivative
at real part three halves. No critical-line assumption or finite truncation
is used. Identifying this series with an integrated xi ratio is a separate step.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex
open scoped ComplexConjugate

/-- The integrated step of one actual xi divisor label, centered at the chosen height. -/
def turingXiLogStep (T : ℝ) (p : RiemannXiDivisorZeroIndex) : ℝ :=
  logNormStepIntegral (riemannXiDivisorZeroValue p - ((1 / 2 : ℂ) + T * I))

private theorem centered_xi_zero_strip (T : ℝ) (p : RiemannXiDivisorZeroIndex) :
    |(riemannXiDivisorZeroValue p - ((1 / 2 : ℂ) + T * I)).re| ≤ 1 / 2 := by
  obtain ⟨hlo, hhi⟩ := riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)
  simp only [sub_re, add_re, div_ofNat_re, one_re, mul_re, ofReal_re, I_re, ofReal_im,
    I_im, mul_zero, zero_mul, sub_self, add_zero]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Each actual integrated zero contribution is nonnegative at every real height. -/
theorem turingXiLogStep_nonneg (T : ℝ) (p : RiemannXiDivisorZeroIndex) :
    0 ≤ turingXiLogStep T p :=
  logNormStepIntegral_nonneg (abs_le.mp (centered_xi_zero_strip T p)).2

private theorem centered_resolvent_pair (T : ℝ) (p : RiemannXiDivisorZeroIndex) :
    (1 / (1 - (riemannXiDivisorZeroValue p - ((1 / 2 : ℂ) + T * I)))).re +
      (1 / (1 + (riemannXiDivisorZeroValue p - ((1 / 2 : ℂ) + T * I)))).re =
    (1 / (((3 / 2 : ℂ) + T * I) - riemannXiDivisorZeroValue p)).re +
      (1 / (((3 / 2 : ℂ) + T * I) -
        riemannXiDivisorZeroValue (riemannXiDivisorSameHeightReflection p))).re := by
  have hm : 1 - (riemannXiDivisorZeroValue p - ((1 / 2 : ℂ) + T * I)) =
      ((3 / 2 : ℂ) + T * I) - riemannXiDivisorZeroValue p := by ring
  have hp : 1 + (riemannXiDivisorZeroValue p - ((1 / 2 : ℂ) + T * I)) =
      conj (((3 / 2 : ℂ) + T * I) -
        riemannXiDivisorZeroValue (riemannXiDivisorSameHeightReflection p)) := by
    rw [riemannXiDivisorZeroValue_sameHeightReflection]
    simp only [map_sub, map_add, map_mul, map_div₀, map_ofNat, conj_ofReal,
      conj_I, map_one, conj_conj]
    ring
  rw [hm, hp]
  simp only [one_div, ← map_inv₀, conj_re]

private theorem turingXiLogStep_le_pair (T : ℝ) (p : RiemannXiDivisorZeroIndex) :
    turingXiLogStep T p ≤ 16 *
      ((1 / (((3 / 2 : ℂ) + T * I) - riemannXiDivisorZeroValue p)).re +
        (1 / (((3 / 2 : ℂ) + T * I) -
          riemannXiDivisorZeroValue (riemannXiDivisorSameHeightReflection p))).re) := by
  have h := logNormStepIntegral_le_resolvent_pair (centered_xi_zero_strip T p)
  rwa [centered_resolvent_pair] at h

/-- The complete logarithmic-step family is summable, with every divisor multiplicity retained. -/
theorem summable_turingXiLogStep (T : ℝ) : Summable (turingXiLogStep T) := by
  have hr := summable_re_xi_divisor_resolvent ((3 / 2 : ℂ) + T * I)
  exact Summable.of_nonneg_of_le (turingXiLogStep_nonneg T) (turingXiLogStep_le_pair T)
    ((hr.add (hr.comp_injective riemannXiDivisorSameHeightReflection.injective)).mul_left 16)

private theorem reflected_log_step (T : ℝ) (p : RiemannXiDivisorZeroIndex) :
    turingXiLogStep T (riemannXiDivisorSameHeightReflection p) =
      logNormStepIntegral (-(riemannXiDivisorZeroValue p - ((1 / 2 : ℂ) + T * I))) := by
  have he : riemannXiDivisorZeroValue (riemannXiDivisorSameHeightReflection p) -
      ((1 / 2 : ℂ) + T * I) =
      star (-(riemannXiDivisorZeroValue p - ((1 / 2 : ℂ) + T * I))) := by
    rw [riemannXiDivisorZeroValue_sameHeightReflection]
    simp only [star_def, map_neg, map_sub, map_add, map_mul, map_div₀, map_ofNat,
      map_one, conj_ofReal, conj_I]
    ring
  rw [turingXiLogStep, he, logNormStepIntegral_conj]

/-- The paired actual contributions satisfy the same constant-sixteen estimate. -/
theorem turingXiLogStep_pair_le (T : ℝ) (p : RiemannXiDivisorZeroIndex) :
    turingXiLogStep T p + turingXiLogStep T (riemannXiDivisorSameHeightReflection p) ≤
      16 * ((1 / (((3 / 2 : ℂ) + T * I) - riemannXiDivisorZeroValue p)).re +
        (1 / (((3 / 2 : ℂ) + T * I) -
          riemannXiDivisorZeroValue (riemannXiDivisorSameHeightReflection p))).re) := by
  rw [reflected_log_step]
  have h := logNormStepIntegral_pair_le (centered_xi_zero_strip T p)
  rwa [centered_resolvent_pair] at h

/-- The complete spectral budget is bounded by the actual right-half-plane xi derivative. -/
theorem tsum_turingXiLogStep_le (T : ℝ) :
    (∑' p, turingXiLogStep T p) ≤ 16 * (logDeriv riemannXi ((3 / 2 : ℂ) + T * I)).re := by
  let r := fun p : RiemannXiDivisorZeroIndex =>
    (1 / (((3 / 2 : ℂ) + T * I) - riemannXiDivisorZeroValue p)).re
  have hr : Summable r := summable_re_xi_divisor_resolvent _
  have hf := summable_turingXiLogStep T
  have h := Summable.tsum_le_tsum (turingXiLogStep_pair_le T)
    (hf.add (hf.comp_injective riemannXiDivisorSameHeightReflection.injective))
    ((hr.add (hr.comp_injective riemannXiDivisorSameHeightReflection.injective)).mul_left 16)
  have hsf := hf.tsum_add (hf.comp_injective riemannXiDivisorSameHeightReflection.injective)
  have hsr := hr.tsum_add (hr.comp_injective riemannXiDivisorSameHeightReflection.injective)
  simp only [Function.comp_apply] at hsf hsr
  change (∑' p, (turingXiLogStep T p +
    turingXiLogStep T (riemannXiDivisorSameHeightReflection p))) ≤
      ∑' p, 16 * (r p + r (riemannXiDivisorSameHeightReflection p)) at h
  rw [hsf, riemannXiDivisorSameHeightReflection.tsum_eq, tsum_mul_left,
    hsr, riemannXiDivisorSameHeightReflection.tsum_eq] at h
  have hxi : riemannXi ((3 / 2 : ℂ) + T * I) ≠ 0 :=
    riemannXi_ne_zero_of_one_lt_re (by norm_num)
  rw [re_logDeriv_riemannXi_eq_tsum_resolvent hxi]
  change (∑' p, turingXiLogStep T p) ≤ 16 * ∑' p, r p
  linarith

end

end PrimeFactorUnimodality
