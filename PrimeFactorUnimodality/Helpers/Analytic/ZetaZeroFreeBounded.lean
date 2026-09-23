import PrimeFactorUnimodality.Helpers.Analytic.XiSmallHeightExclusion
import PrimeFactorUnimodality.Helpers.Analytic.ZetaZeroFreeInitial

/-! # An unconditional initial gap throughout each bounded xi strip

The real Hadamard mass excludes absolute heights at most one. On the
remaining bounded strip the same `3,4,1` argument as the high-height
initial region uses the upper height in its logarithmic budget. This
supplies a weak but unconditional fixed low-height gap. It does not
assert a finite-height RH verification or Dusart's optimized constant.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

private theorem bounded_pole_le_one {σ t : ℝ} (hσ : 1 < σ) (hσ₂ : σ ≤ 2)
    (ht : 1 ≤ |t|) : zeroFreePoleTerm σ t ≤ 1 := by
  have ht₂ : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
  unfold zeroFreePoleTerm
  apply (div_le_iff₀ (by positivity : 0 < (σ - 1) ^ 2 + t ^ 2)).mpr
  nlinarith [sq_nonneg (σ - 1)]

/-- The elementary remainder is bounded uniformly between heights one and the cutoff. -/
theorem zeroFree_three_four_one_error_le_cutoff {σ t T : ℝ}
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (ht : 1 ≤ |t|) (htT : |t| ≤ T) (hT : 10 ^ 9 ≤ T) :
    3 - (5 / 2 : ℝ) * (Real.log (4 * π) - Real.eulerMascheroniConstant - 2) +
      4 * zeroFreePoleTerm σ t + zeroFreePoleTerm σ (2 * t) +
      4 * zeroFreeGammaTerm t + zeroFreeGammaTerm (2 * t) ≤ 4 * Real.log T := by
  have hTpos : 0 < T := by linarith
  have hlog := seventeen_le_log_of_billion_le hT
  have hpi : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hfourpi : 0 ≤ Real.log (4 * π) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hc : 3 - (5 / 2 : ℝ) *
      (Real.log (4 * π) - Real.eulerMascheroniConstant - 2) ≤ 11 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hp := bounded_pole_le_one hσ hσ₂ ht
  have hp₂ := bounded_pole_le_one hσ hσ₂ (t := 2 * t)
    (by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith)
  have hlg : Real.log (|t| / 2 + 3) ≤ Real.log T :=
    Real.log_le_log (by positivity) (by linarith)
  have hg : zeroFreeGammaTerm t ≤ Real.log T / 2 + 1 / 2 := by
    unfold zeroFreeGammaTerm
    linarith
  have hl₂ : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlg₂ : Real.log (|2 * t| / 2 + 3) ≤ Real.log T + 1 := by
    calc
      _ ≤ Real.log (2 * T) := Real.log_le_log (by positivity) (by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith)
      _ = Real.log 2 + Real.log T := Real.log_mul (by norm_num) hTpos.ne'
      _ ≤ _ := by linarith
  have hg₂ : zeroFreeGammaTerm (2 * t) ≤ Real.log T / 2 + 1 := by
    unfold zeroFreeGammaTerm
    linarith
  linarith only [hc, hp, hp₂, hg, hg₂, hlog]

/-- All zeros below the cutoff have a proved positive gap, without finite zero data. -/
theorem xi_zero_gap_bounded {T : ℝ} (hT : 10 ^ 9 ≤ T) {ρ : ℂ}
    (hρ : riemannXi ρ = 0) (ht : |ρ.im| ≤ T) : 1 / (56 * Real.log T) ≤ 1 - ρ.re := by
  let L := Real.log T
  have hL : 17 ≤ L := seventeen_le_log_of_billion_le hT
  have hLpos : 0 < L := by linarith
  let σ := 1 + 1 / (8 * L)
  have hσ : 1 < σ := by
    have hp : 0 < 1 / (8 * L) := by positivity
    dsimp [σ]
    linarith
  have hσ₂ : σ ≤ 2 := by
    have h := (div_le_iff₀ (by positivity : 0 < 8 * L)).mpr
      (by linarith : (1 : ℝ) ≤ 1 * (8 * L))
    dsimp [σ]
    linarith
  have he := zeroFree_three_four_one_error_le_cutoff hσ hσ₂
    (one_lt_abs_im_of_xi_zero hρ).le ht hT
  have hc := xi_zero_three_four_one_constraint hρ hσ hσ₂
  have hdiv : 3 / (σ - 1) = 24 * L := by dsimp [σ]; field_simp; ring
  have hbound : 4 / (σ - ρ.re) ≤ 28 * L := by
    rw [hdiv] at hc
    dsimp [L] at *
    linarith only [he, hc]
  have hden : 0 < σ - ρ.re := by linarith [(riemannXi_zero_mem_critical_strip hρ).2]
  have hmul := (div_le_iff₀ hden).mp hbound
  have hscale : L * (σ - 1) = 1 / 8 := by dsimp [σ]; field_simp; ring
  apply (div_le_iff₀ (by positivity : 0 < 56 * L)).mpr
  nlinarith only [hmul, hscale]

/-- A single unconditional formula covers every actual xi zero, including low heights. -/
theorem xi_zero_gap_initial_all_heights {ρ : ℂ} (hρ : riemannXi ρ = 0) :
    1 / (56 * Real.log (max (10 ^ 9) |ρ.im|)) ≤ 1 - ρ.re :=
  xi_zero_gap_bounded (le_max_left _ _) hρ (le_max_right _ _)

/-- The strict finite prefix inherits the explicit initial gap at its cutoff. -/
theorem xi_low_re_le_initial_gap {H : ℝ} (hH : 10 ^ 9 ≤ H)
    (p : RiemannXiDivisorZeroIndex) (hp : p ∈ xiLowHeightIndices H) :
    (riemannXiDivisorZeroValue p).re ≤ 1 - 1 / (56 * Real.log H) := by
  have hg := xi_zero_gap_bounded hH (riemannXiDivisorZeroValue_eq_zero p)
    ((mem_xiLowHeightIndices H p).mp hp).le
  linarith

end

end PrimeFactorUnimodality
