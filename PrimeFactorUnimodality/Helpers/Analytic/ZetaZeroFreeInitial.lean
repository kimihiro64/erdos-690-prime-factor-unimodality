import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanHigh
import PrimeFactorUnimodality.Helpers.Analytic.ZetaZeroFreeInequality

/-! # A proved initial numerical zero-free region at high heights

Optimize the existing actual `3,4,1` constraint at
`sigma=1+1/(8*log(abs(t)))`. Its elementary error is at most `4*log(abs(t))`
above `10^9`, giving the unconditional initial constant `56`.
This is a starting region for the smoothed bootstrap, not the final
Mossinghoff--Trudgian constant. Low-height information remains separate.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

private theorem initial_pole_le_one {σ t : ℝ} (hσ : 1 < σ) (hσ₂ : σ ≤ 2)
    (ht : 1 ≤ |t|) : zeroFreePoleTerm σ t ≤ 1 := by
  have ht₂ : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
  unfold zeroFreePoleTerm
  apply (div_le_iff₀ (by positivity : 0 < (σ - 1) ^ 2 + t ^ 2)).mpr
  nlinarith [sq_nonneg (σ - 1)]

/-- The remaining terms of the classical constraint have an explicit logarithmic budget. -/
theorem zeroFree_three_four_one_error_le_four_log {σ t : ℝ}
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (ht : 10 ^ 9 ≤ |t|) :
    3 - (5 / 2 : ℝ) * (Real.log (4 * π) - Real.eulerMascheroniConstant - 2) +
      4 * zeroFreePoleTerm σ t + zeroFreePoleTerm σ (2 * t) +
      4 * zeroFreeGammaTerm t + zeroFreeGammaTerm (2 * t) ≤ 4 * Real.log |t| := by
  have htpos : 0 < |t| := by linarith
  have hlog := seventeen_le_log_of_billion_le ht
  have hpi : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hfourpi : 0 ≤ Real.log (4 * π) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hc : 3 - (5 / 2 : ℝ) *
      (Real.log (4 * π) - Real.eulerMascheroniConstant - 2) ≤ 11 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hp := initial_pole_le_one hσ hσ₂ (t := t) (by linarith)
  have hp₂ := initial_pole_le_one hσ hσ₂ (t := 2 * t)
    (by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith)
  have hlg : Real.log (|t| / 2 + 3) ≤ Real.log |t| :=
    Real.log_le_log (by positivity) (by linarith)
  have hg : zeroFreeGammaTerm t ≤ Real.log |t| / 2 + 1 / 2 := by
    unfold zeroFreeGammaTerm
    linarith
  have hl₂ : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlg₂ : Real.log (|2 * t| / 2 + 3) ≤ Real.log |t| + 1 := by
    calc
      _ ≤ Real.log (2 * |t|) := Real.log_le_log (by positivity) (by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith)
      _ = Real.log 2 + Real.log |t| := Real.log_mul (by norm_num) htpos.ne'
      _ ≤ _ := by linarith
  have hg₂ : zeroFreeGammaTerm (2 * t) ≤ Real.log |t| / 2 + 1 := by
    unfold zeroFreeGammaTerm
    linarith
  linarith only [hc, hp, hp₂, hg, hg₂, hlog]

/-- An actual high xi zero stays at least `1/(56*log(abs(height)))` from the line one. -/
theorem xi_zero_gap_initial {ρ : ℂ} (hρ : riemannXi ρ = 0)
    (ht : 10 ^ 9 ≤ |ρ.im|) : 1 / (56 * Real.log |ρ.im|) ≤ 1 - ρ.re := by
  let L := Real.log |ρ.im|
  have hL : 17 ≤ L := seventeen_le_log_of_billion_le ht
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
  have he := zeroFree_three_four_one_error_le_four_log hσ hσ₂ ht
  have hc := xi_zero_three_four_one_constraint hρ hσ hσ₂
  have hdiv : 3 / (σ - 1) = 24 * L := by dsimp [σ]; field_simp; ring
  have hbound : 4 / (σ - ρ.re) ≤ 28 * L := by
    rw [hdiv] at hc
    dsimp [L] at *
    linarith only [he, hc]
  have hden : 0 < σ - ρ.re := by linarith [(riemannXi_zero_mem_critical_strip hρ).2]
  have hmul := (div_le_iff₀ hden).mp hbound
  have hscale : L * (σ - 1) = 1 / 8 := by
    dsimp [σ]
    field_simp
    ring
  apply (div_le_iff₀ (by positivity : 0 < 56 * L)).mpr
  nlinarith only [hmul, hscale]

/-- The initial region excludes actual xi zeros without a zero-free-region premise. -/
theorem riemannXi_ne_zero_initial {s : ℂ} (ht : 10 ^ 9 ≤ |s.im|)
    (hs : 1 - 1 / (56 * Real.log |s.im|) < s.re) : riemannXi s ≠ 0 := by
  intro hz
  linarith [xi_zero_gap_initial hz ht]

end

end PrimeFactorUnimodality
