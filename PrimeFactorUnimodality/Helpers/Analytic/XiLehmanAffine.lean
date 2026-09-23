import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanBudget

/-! # Uniform logarithmic envelopes for the Lehman tail

The positive-height tail need not decrease with height. Bound it instead
by an explicit affine function of `log(t)` for `t>=T>=2`, `H>=4`.
This keeps the height dependence needed when the bootstrap later uses
an upper bound on `eta*log(t)` obtained from failure of its target gap.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Coefficient of the logarithm in the positive-height tail envelope. -/
def xiLehmanLogCoefficient (T H : ℝ) : ℝ :=
  1 / (π * H) + 1 / (2 * π * T) + 8 / H ^ 2

/-- The constant term in the same envelope. -/
def xiLehmanAffineConstant (T H : ℝ) : ℝ :=
  H / T * (1 / (π * H) + 8 / H ^ 2) + 4 / (T * H) + 68 / H ^ 2

/-- The logarithmic coefficient is nonnegative at positive parameters. -/
theorem xiLehmanLogCoefficient_nonneg {T H : ℝ} (hT : 0 < T) (hH : 0 < H) :
    0 ≤ xiLehmanLogCoefficient T H := by unfold xiLehmanLogCoefficient; positivity

/-- The constant term is nonnegative at positive parameters. -/
theorem xiLehmanAffineConstant_nonneg {T H : ℝ} (hT : 0 < T) (hH : 0 < H) :
    0 ≤ xiLehmanAffineConstant T H := by unfold xiLehmanAffineConstant; positivity

/-- The affine envelope also reserves the full additive counting-error budget. -/
theorem xiLehmanHighBound_add_le_affine {T t H : ℝ}
    (hT : 2 ≤ T) (ht : T ≤ t) (hH : 4 ≤ H) :
    xiLehmanHighBound t H + 68 / H ^ 2 ≤ xiLehmanLogCoefficient T H * Real.log t +
      xiLehmanAffineConstant T H := by
  have hTpos : 0 < T := by linarith
  have htpos : 0 < t := hTpos.trans_le ht
  have hHpos : 0 < H := by linarith
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  let L := Real.log t + H / T
  have hL : 0 ≤ L := add_nonneg hlogt (by positivity)
  have hlog : Real.log (t + H) ≤ L := by
    have he : t + H = t * (1 + H / t) := by field_simp
    have hx : 0 < 1 + H / t := by positivity
    rw [he, Real.log_mul htpos.ne' hx.ne']
    have hl := Real.log_le_sub_one_of_pos hx
    have hh := div_le_div_of_nonneg_left hHpos.le hTpos ht
    dsimp only [L]
    linarith
  have hlog₁ : Real.log ((H + t) / (2 * π)) ≤ L := by
    have hn : (H + t) / (2 * π) ≤ t + H := by
      have h := div_le_self (by positivity : 0 ≤ H + t)
        (by linarith [pi_gt_three] : 1 ≤ 2 * π)
      linarith
    exact (Real.log_le_log (by positivity) hn).trans hlog
  have hlog₂ : Real.log ((H + 2 * t) / H) / t ≤ Real.log t / T := by
    have hr : (H + 2 * t) / H ≤ t := by
      apply (div_le_iff₀ hHpos).mpr
      nlinarith [mul_nonneg (by linarith : 0 ≤ t - 2) (by linarith : 0 ≤ H - 2)]
    have hl := Real.log_le_log (by positivity : 0 < (H + 2 * t) / H) hr
    exact (div_le_div_of_nonneg_right hl htpos.le).trans
      (div_le_div_of_nonneg_left hlogt hTpos ht)
  have hrec : 1 / H + 1 / (H + 2 * t) ≤ 2 / H := by
    have h := one_div_le_one_div_of_le hHpos (by linarith : H ≤ H + 2 * t)
    simp only [div_eq_mul_inv, one_mul] at h ⊢
    linarith only [h]
  have hsq : 1 / H ^ 2 + 1 / (H + 2 * t) ^ 2 ≤ 2 / H ^ 2 := by
    have h := one_div_le_one_div_of_le (sq_pos_of_pos hHpos)
      (sq_le_sq₀ hHpos.le (by positivity) |>.mpr (by linarith : H ≤ H + 2 * t))
    simp only [div_eq_mul_inv, one_mul] at h ⊢
    linarith only [h]
  have hfirst := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul hlog₁ hrec (by positivity) hL) hlog₂)
    (by positivity : 0 ≤ 1 / (2 * π))
  have hsecond := mul_le_mul_of_nonneg_left (mul_le_mul hlog hsq (by positivity) hL)
    (by norm_num : (0 : ℝ) ≤ 4)
  have hlast : 4 / (t * H) ≤ 4 / (T * H) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hTpos hHpos)
      (mul_le_mul_of_nonneg_right ht hHpos.le)
  calc
    _ ≤ (1 / (2 * π)) * (L * (2 / H) + Real.log t / T) +
        4 * L * (2 / H ^ 2) + 4 / (T * H) + 68 / H ^ 2 := by
      unfold xiLehmanHighBound
      nlinarith only [hfirst, hsecond, hlast]
    _ = _ := by
      dsimp only [L, xiLehmanLogCoefficient, xiLehmanAffineConstant]
      simp only [div_eq_mul_inv, mul_inv_rev]
      norm_num
      ring

/-- The former high-height expression remains covered by the same envelope. -/
theorem xiLehmanHighBound_le_affine {T t H : ℝ}
    (hT : 2 ≤ T) (ht : T ≤ t) (hH : 4 ≤ H) :
    xiLehmanHighBound t H ≤ xiLehmanLogCoefficient T H * Real.log t +
      xiLehmanAffineConstant T H :=
  (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ 68 / H ^ 2)).trans
    (xiLehmanHighBound_add_le_affine hT ht hH)

/-- The complete logarithmic discrepancy costs at most an explicit constant increment. -/
theorem xiLehmanLogBound_le_highBound_add {t H : ℝ}
    (ht : 0 < t) (hH : 0 < H) (hA : 1 ≤ t + H) :
    xiLehmanLogBound t H ≤ xiLehmanHighBound t H + 68 / H ^ 2 := by
  have hsq : 1 / H ^ 2 + 1 / (H + 2 * t) ^ 2 ≤ 2 / H ^ 2 := by
    have h := one_div_le_one_div_of_le (sq_pos_of_pos hH)
      (sq_le_sq₀ hH.le (by positivity) |>.mpr (by linarith : H ≤ H + 2 * t))
    simp only [div_eq_mul_inv, one_mul] at h ⊢
    linarith only [h]
  have hlog := mul_nonneg (Real.log_nonneg hA)
    (by positivity : (0 : ℝ) ≤ 1 / H ^ 2 + 1 / (H + 2 * t) ^ 2)
  have hlast : (0 : ℝ) ≤ 2 / (t * H) := by positivity
  unfold xiLehmanLogBound xiLehmanHighBound
  simp only [div_eq_mul_inv] at hsq hlog hlast ⊢
  nlinarith only [hsq, hlog, hlast]

/-- At the former logarithmic threshold the new bound improves the old one. -/
theorem xiLehmanLogBound_le_highBound {t H : ℝ}
    (ht : 0 < t) (hH : 0 < H) (hlog : 17 ≤ Real.log (t + H)) :
    xiLehmanLogBound t H ≤ xiLehmanHighBound t H := by
  have h := mul_le_mul_of_nonneg_right
    (by linarith : 2 * Real.log (t + H) + 34 ≤ 4 * Real.log (t + H))
    (by positivity : (0 : ℝ) ≤ 1 / H ^ 2 + 1 / (H + 2 * t) ^ 2)
  have hlast : (0 : ℝ) ≤ 2 / (t * H) := by positivity
  unfold xiLehmanLogBound xiLehmanHighBound
  simp only [div_eq_mul_inv] at h hlast ⊢
  nlinarith only [h, hlast]

/-- The moderate-height bound is compatible with the existing correction polynomial. -/
theorem xiLehmanLogBound_le_affine {T t H : ℝ}
    (hT : 2 ≤ T) (ht : T ≤ t) (hH : 4 ≤ H) :
    xiLehmanLogBound t H ≤ xiLehmanLogCoefficient T H * Real.log t +
      xiLehmanAffineConstant T H :=
  (xiLehmanLogBound_le_highBound_add (by linarith) (by linarith) (by linarith)).trans
    (xiLehmanHighBound_add_le_affine hT ht hH)

end

end PrimeFactorUnimodality
