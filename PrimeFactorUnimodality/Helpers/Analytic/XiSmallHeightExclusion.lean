import PrimeFactorUnimodality.Helpers.Analytic.XiLowReciprocalMass

/-! # Excluding the initial unit-height xi strip by its total reciprocal mass

The unconditional real Hadamard identity bounds the entire reciprocal mass
by `1/3`. A zero with real part at least one half and absolute ordinate at
most one would contribute at least `1/3` by itself. Reflection handles the
other half of the critical strip. No finite zero enumeration is required.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- A coarse unconditional upper bound already excludes the initial unit-height strip. -/
theorem tsum_re_xi_divisor_reciprocal_lt_third :
    (∑' p : RiemannXiDivisorZeroIndex, (1 / riemannXiDivisorZeroValue p).re) < 1 / 3 := by
  have he : Real.exp (2 : ℝ) < 9 := by
    have hp := Real.exp_one_lt_three
    have hpos := Real.exp_pos 1
    have hid : Real.exp (2 : ℝ) = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [hid]
    nlinarith
  have hl : (2 : ℝ) < Real.log (4 * π) :=
    (Real.lt_log_iff_exp_lt (by positivity)).mpr (he.trans (by linarith [Real.pi_gt_three]))
  have hs := re_logDeriv_riemannXi_zero_eq_neg_tsum_reciprocal
  rw [re_logDeriv_riemannXi_zero_eq] at hs
  linarith [Real.eulerMascheroniConstant_lt_two_thirds]

private theorem one_lt_abs_im_of_re_half (p : RiemannXiDivisorZeroIndex)
    (hβ : 1 / 2 ≤ (riemannXiDivisorZeroValue p).re) :
    1 < |(riemannXiDivisorZeroValue p).im| := by
  by_contra h
  have hγ : |(riemannXiDivisorZeroValue p).im| ≤ 1 := le_of_not_gt h
  obtain ⟨hβ0, hβ1⟩ := riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)
  have hγ2 : (riemannXiDivisorZeroValue p).im ^ 2 ≤ 1 := by
    nlinarith [sq_abs (riemannXiDivisorZeroValue p).im,
      abs_nonneg (riemannXiDivisorZeroValue p).im]
  have hβ2 : (riemannXiDivisorZeroValue p).re ^ 2 ≤ (riemannXiDivisorZeroValue p).re := by
    nlinarith
  have hd : 0 < normSq (riemannXiDivisorZeroValue p) :=
    normSq_pos.mpr (riemannXiDivisorZeroValue_ne_zero p)
  have hp : 1 / 3 ≤ (1 / riemannXiDivisorZeroValue p).re := by
    rw [one_div (riemannXiDivisorZeroValue p), inv_re]
    apply (le_div_iff₀ hd).mpr
    rw [normSq_apply]
    nlinarith
  have hs := summable_re_xi_divisor_reciprocal.le_tsum p
    (fun q _ => re_xi_divisor_reciprocal_nonneg q)
  linarith [tsum_re_xi_divisor_reciprocal_lt_third]

/-- Every actual divisor label has absolute ordinate strictly above one. -/
theorem one_lt_abs_im_xi_divisor (p : RiemannXiDivisorZeroIndex) :
    1 < |(riemannXiDivisorZeroValue p).im| := by
  by_cases hβ : 1 / 2 ≤ (riemannXiDivisorZeroValue p).re
  · exact one_lt_abs_im_of_re_half p hβ
  · have h := one_lt_abs_im_of_re_half (riemannXiDivisorReflection p) (by
      rw [riemannXiDivisorZeroValue_reflection, sub_re, one_re]
      linarith)
    simpa only [riemannXiDivisorZeroValue_reflection, sub_im, one_im, zero_sub, abs_neg] using h

/-- The exclusion also applies to any actual zero, without choosing a divisor enumeration. -/
theorem one_lt_abs_im_of_xi_zero {ρ : ℂ} (hρ : riemannXi ρ = 0) : 1 < |ρ.im| := by
  obtain ⟨p, rfl⟩ := exists_xi_divisor_index_of_zero hρ
  exact one_lt_abs_im_xi_divisor p

end

end PrimeFactorUnimodality
