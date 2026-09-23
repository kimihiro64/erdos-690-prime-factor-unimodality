import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPowerBudget
import PrimeFactorUnimodality.Helpers.Analytic.DusartEarlierCutoffScalars

/-! # A complete psi budget at an earlier transition point

Order three and step 1/50000 use the new inner mass and complete power tails.
A square lower bound controls each starting point, so both adjacent averages
are retained. Only the original low-height zero-location premise remains in
the resulting actual psi estimate.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Both adjacent smoothing widths fit in this common interval. -/
theorem dusartEarlier_width_le {s : ℝ} (hs : s ≤ (1 / 49997 : ℝ)) :
    1 + 3 * s ≤ (10001 / 10000 : ℝ) := by linarith

/-- One coefficient bounds the fourth-power tails at both starting points. -/
theorem dusartEarlier_high_coefficient_le {s : ℝ} (hs₀ : (1 / 50000 : ℝ) ≤ s)
    (hs₁ : s ≤ (1 / 49997 : ℝ)) :
    8 * (1 + 3 * s) ^ 4 / s ^ 3 ≤ (1001 * 10 ^ 12 : ℝ) := by
  have hspos : 0 < s := by linarith
  have hn := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 3 * s) (dusartEarlier_width_le hs₁) 4
  have hd := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 50000) hs₀ 3
  calc
    _ ≤ 8 * (10001 / 10000 : ℝ) ^ 4 / s ^ 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) (by positivity)
    _ ≤ 8 * (10001 / 10000 : ℝ) ^ 4 / (1 / 50000 : ℝ) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
    _ ≤ _ := by norm_num

/-- Rational majorant for one average at a point at least `r ^ 2`. -/
def dusartEarlierAverageCap (r : ℝ) : ℝ :=
  ((10001 / 10000) * (91 / 5) + (1001 * 10 ^ 12) * (11 / 10 ^ 16)) / r +
    (1001 * 10 ^ 12) * (11 / 10 ^ 23) + 4 / r ^ 2

/-- The complete average has an explicit cap, including the elementary correction. -/
theorem dusartBoxPowerRelativeBudget_earlier_le {s x r : ℝ}
    (hs₀ : (1 / 50000 : ℝ) ≤ s) (hs₁ : s ≤ (1 / 49997 : ℝ))
    (hr : 2 ≤ r) (hx : r ^ 2 ≤ x) :
    dusartBoxPowerRelativeBudget 0 s x 25 100000 25000000 (1 / 2) ≤
      dusartEarlierAverageCap r := by
  have hrpos : 0 < r := by linarith
  have hx4 : 4 ≤ x := by nlinarith
  have hxpos : 0 < x := by linarith
  have hspos : 0 < s := by linarith
  have hl := Real.log_le_log (pow_pos hrpos 2) hx
  rw [Real.log_pow] at hl
  have he : exp (-(1 / 2) * log x) ≤ 1 / r := by
    have h := Real.exp_le_exp.mpr (show -(1 / 2) * log x ≤ -log r by norm_num at hl; linarith)
    simpa only [Real.exp_neg, Real.exp_log hrpos, one_div] using h
  have hc := dusartEarlier_high_coefficient_le hs₀ hs₁
  have hc0 : 0 ≤ 8 * (1 + 3 * s) ^ 4 / s ^ 3 := by positivity
  have hlow : (1 + 3 * s) * xiLowReciprocalNormBound 25 100000 (1 / 2) ≤
      (10001 / 10000 : ℝ) * (91 / 5) :=
    (mul_le_mul_of_nonneg_left xiLowReciprocalNormBound_early_le (by positivity)).trans
      (mul_le_mul_of_nonneg_right (dusartEarlier_width_le hs₁) (by norm_num))
  have hband : (8 * (1 + 3 * s) ^ 4 / s ^ 3) * xiRosserPowerTailBound 4 100000 ≤
      (1001 * 10 ^ 12 : ℝ) * (11 / 10 ^ 16) :=
    (mul_le_mul_of_nonneg_left xiRosserPowerTailBound_four_early_inner_le hc0).trans
      (mul_le_mul_of_nonneg_right hc (by norm_num))
  have hhigh : (8 * (1 + 3 * s) ^ 4 / s ^ 3) * xiRosserPowerTailBound 4 25000000 ≤
      (1001 * 10 ^ 12 : ℝ) * (11 / 10 ^ 23) :=
    (mul_le_mul_of_nonneg_left xiRosserPowerTailBound_four_early_outer_le hc0).trans
      (mul_le_mul_of_nonneg_right hc (by norm_num))
  have hsplit : dusartBoxSplitLowBound 0 s x 25 100000 25000000 (1 / 2) ≤
      ((10001 / 10000 : ℝ) * (91 / 5) + (1001 * 10 ^ 12) * (11 / 10 ^ 16)) / r := by
    unfold dusartBoxSplitLowBound xiRosserPowerBandBound
    norm_num only [Nat.cast_ofNat, zero_add, show (100000 : ℝ) < 25000000 by norm_num,
      ite_true, show (2 : ℝ) ^ (3 : ℕ) = 8 by norm_num]
    exact ((mul_le_mul_of_nonneg_left (add_le_add hlow hband) (exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right he (by norm_num))).trans_eq (by ring)
  have hcorr : (1 / (2 * (x ^ 2 - 1)) + log (2 * π)) / x ≤ 4 / r ^ 2 := by
    have hd : 1 ≤ 2 * (x ^ 2 - 1) := by nlinarith
    have hi : 1 / (2 * (x ^ 2 - 1)) ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd
    have hlog : log (2 * π) ≤ 3 := by
      have h := log_le_log (by positivity : 0 < 2 * π)
        (by linarith [pi_lt_four] : 2 * π ≤ 2 ^ 3)
      rw [log_pow] at h
      norm_num at h
      linarith [log_two_lt_d9]
    exact (div_le_div_of_nonneg_right (by linarith : 1 / (2 * (x ^ 2 - 1)) +
      log (2 * π) ≤ 4) hxpos.le).trans
        (div_le_div_of_nonneg_left (by norm_num) (pow_pos hrpos 2) hx)
  unfold dusartBoxPowerRelativeBudget dusartEarlierAverageCap
  simp only [Nat.cast_ofNat, zero_add, show (2 : ℝ) ^ (3 : ℕ) = 8 by norm_num]
  exact add_le_add (add_le_add ((min_le_right _ _).trans hsplit) hhigh) hcorr

/-- Both averages and the exact smoothing loss are included in the pointwise cap. -/
theorem dusartBoxPowerPsiBound_earlier_le {x₀ r : ℝ} (hr : 2 ≤ r)
    (hx₀ : r ^ 2 ≤ x₀ * (1 - 3 * (1 / 50000))) :
    dusartBoxPowerPsiBound 0 (1 / 50000) x₀ 25 100000 25000000 (1 / 2) ≤
      dusartEarlierAverageCap r + 3 / 100000 := by
  have hxpos : 0 < x₀ := by nlinarith [sq_nonneg r]
  have hx : r ^ 2 ≤ x₀ := by nlinarith
  have hl := dusartBoxPowerRelativeBudget_earlier_le
    (s := (1 / 50000) / (1 - 3 * (1 / 50000))) (by norm_num) (by norm_num) hr hx₀
  have hu := dusartBoxPowerRelativeBudget_earlier_le
    (s := 1 / 50000) (by norm_num) (by norm_num) hr hx
  have hcap : 0 ≤ dusartEarlierAverageCap r := by unfold dusartEarlierAverageCap; positivity
  have hl' : (1 - 3 * (1 / 50000) : ℝ) * dusartBoxPowerRelativeBudget 0
      ((1 / 50000) / (1 - 3 * (1 / 50000)))
      (x₀ * (1 - 3 * (1 / 50000))) 25 100000 25000000 (1 / 2) ≤
      dusartEarlierAverageCap r :=
    (mul_le_mul_of_nonneg_left hl (by norm_num)).trans (by nlinarith)
  unfold dusartBoxPowerPsiBound
  norm_num only [Nat.cast_ofNat, zero_add]
  norm_num only at hl'
  exact add_le_add (max_le hl' hu) (by norm_num)

/-- The actual psi bound keeps precisely the existing finite low-zero hypothesis. -/
theorem abs_psi_sub_div_le_earlier {x₀ x r : ℝ} (hr : 2 ≤ r)
    (hx₀ : r ^ 2 ≤ x₀ * (1 - 3 * (1 / 50000))) (hx : x₀ ≤ x)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.psi x - x| / x ≤ dusartEarlierAverageCap r + 3 / 100000 := by
  have hxpos : 0 < x₀ := by nlinarith [sq_nonneg r]
  have hleft : 1 < x₀ * (1 - 3 * (1 / 50000)) := by nlinarith
  exact (abs_psi_sub_div_le_power_frozen (x₀ := x₀) (s := 1 / 50000)
    (a := 25) (U := 100000) (H := 25000000) (δ := 1 / 2)
    0 (by norm_num) hxpos hx hleft (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] using hgap)).trans
      (dusartBoxPowerPsiBound_earlier_le hr hx₀)

end

end PrimeFactorUnimodality
