import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserFixedRelative
import PrimeFactorUnimodality.Helpers.Analytic.DusartLogarithmicScalars
import PrimeFactorUnimodality.Helpers.Analytic.DusartMiddleScalars

/-! # Actual averaged psi error on the entire middle logarithmic band

The fixed billion-height cutoff removes the intermediate zero window.
Its evaluated high tail, low block and correction have total square-log
moment below six hundredths. The numerical region and finite low-zero
verification are explicit inputs; no scalar budget is left unproved.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The existing dimensionless fixed-cutoff budget is uniformly small on the middle band. -/
theorem dusartBoxRosserFixedRelativeBudget_le_middle {s x : ℝ}
    (hx : 1 < x) (hb : 84 ≤ Real.log x) (hb₁ : Real.log x ≤ 5000)
    (hs₀ : (3 / 40 : ℝ) / Real.log x ^ 2 ≤ s)
    (hs₁ : s ≤ (17 / 200 : ℝ) / Real.log x ^ 2) :
    dusartBoxRosserFixedRelativeBudget 0 s x 6 2 10 1000000000 (1 / 2) ≤
      (3 / 50 : ℝ) / Real.log x ^ 2 := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hbpos : 0 < Real.log x := Real.log_pos hx
  have hspos : 0 < s := (by positivity : 0 < (3 / 40 : ℝ) / Real.log x ^ 2).trans_le hs₀
  have hx2 : 2 ≤ x := by
    have he := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hxpos] at he
    linarith
  have hw : 1 + 3 * s ≤ (11 / 10 : ℝ) := (dusartMiddle_width_le hb hs₁).trans (by norm_num)
  have hl : ((1 + 3 * s) * exp (-(1 / 2) * Real.log x)) *
      xiLowReciprocalNormBound 10 1000000000 (1 / 2) ≤ 77 * exp (-Real.log x / 2) := by
    calc
      _ ≤ ((1 + 3 * s) * exp (-(1 / 2) * Real.log x)) * 70 :=
        mul_le_mul_of_nonneg_left xiLowReciprocalNormBound_billion_half_le (by positivity)
      _ ≤ ((11 / 10 : ℝ) * exp (-(1 / 2) * Real.log x)) * 70 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw (exp_pos _).le) (by norm_num)
      _ = _ := by rw [show -(1 / 2) * Real.log x = -Real.log x / 2 by ring]; ring
  have hbudget : dusartBoxRosserFixedRelativeBudget 0 s x 6 2 10 1000000000 (1 / 2) ≤
      77 * exp (-Real.log x / 2) + (8 * (1 + 3 * s) ^ 4 / s ^ 3) *
        xiRosserClosedTailBound (Real.log x / 6) 4 2 1000000000 + 4 / x := by
    simpa only [dusartBoxRosserFixedRelativeBudget, Nat.reduceAdd, Nat.cast_ofNat,
      show (2 : ℝ) ^ 3 = 8 by norm_num] using
      add_le_add (add_le_add hl le_rfl) (dusartLog_correction_le hx2)
  have hlow := dusartMiddle_low_moment_le hb
  have hhigh := dusartMiddle_high_moment_le hb hb₁ hs₀ hs₁
  have hcorrection := dusartMiddle_correction_moment_le hb
  rw [Real.exp_log hxpos] at hcorrection
  have hscaled := mul_le_mul_of_nonneg_left hbudget (sq_nonneg (Real.log x))
  apply (le_div_iff₀ (pow_pos hbpos 2)).mpr
  nlinarith only [hlow, hhigh, hcorrection, hscaled]

/-- The actual average satisfies the fully evaluated middle-band estimate. -/
theorem abs_dusartPsiAverageError_div_le_middle {s x : ℝ}
    (hx : 1 < x) (hb : 84 ≤ Real.log x) (hb₁ : Real.log x ≤ 5000)
    (hs₀ : (3 / 40 : ℝ) / Real.log x ^ 2 ≤ s)
    (hs₁ : s ≤ (17 / 200 : ℝ) / Real.log x ^ 2)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError 3 (s * x) x| / x ≤ (3 / 50 : ℝ) / Real.log x ^ 2 := by
  have hbpos : 0 < Real.log x := Real.log_pos hx
  have hspos : 0 < s := (by positivity : 0 < (3 / 40 : ℝ) / Real.log x ^ 2).trans_le hs₀
  have hpeak : exp (sqrt ((Real.log x / 6) / 4)) ≤ (1000000000 : ℝ) :=
    (exp_le_exp.mpr (sqrt_le_sqrt (by linarith :
      (Real.log x / 6) / 4 ≤ (Real.log x / 6) / (4 - 2)))).trans
        (dusartMiddle_cutoff_branch hb₁)
  have h := abs_dusartPsiAverageError_div_le_rosserFixed 0 hspos hx
    (by norm_num : (0 : ℝ) < 6) (by norm_num : (1 : ℝ) < 2) (by norm_num)
    (by norm_num : (10 : ℝ) ≤ 10) (by norm_num : (10 : ℝ) < 1000000000)
    (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2)
    (by simpa only [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] using hgap) hpeak hreg
  exact h.trans (dusartBoxRosserFixedRelativeBudget_le_middle hx hb hb₁ hs₀ hs₁)

end

end PrimeFactorUnimodality
