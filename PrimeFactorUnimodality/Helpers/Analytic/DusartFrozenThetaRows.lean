import PrimeFactorUnimodality.Helpers.Analytic.DusartEarlierCutoffTheta
import PrimeFactorUnimodality.Helpers.Analytic.DusartFrozenLogBudget
import PrimeFactorUnimodality.Helpers.Analytic.DusartSharperRootCorrection

/-! # Compact scalar rows covering whole logarithmic theta intervals

Each row stores only its two logarithmic endpoints and three smoothing
parameters. Its validity concerns elementary scalar bounds, independently of
zero data. One reusable analytic proof then controls every real point in the
row, including prime-power jumps. No interior integer is enumerated.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The logarithmic band starts inside the proved sharper-root domain. -/
theorem dusartFrozen_exp_twentyFive_ge : (3000000000 : ℝ) ≤ exp 25 := by
  calc
    _ ≤ (5 / 2 : ℝ) ^ 25 := by norm_num
    _ ≤ exp (1 : ℝ) ^ 25 := pow_le_pow_left₀ (by norm_num)
      (by linarith [exp_one_gt_d9]) 25
    _ = _ := by rw [← exp_nat_mul]; norm_num

/-- Every smoothing order has its complete-tail turning height below the reduced cutoff. -/
theorem dusartFrozen_peak_le (m : ℕ) {b H : ℝ}
    (hb : 0 ≤ b) (hb₁ : b ≤ 5000) (hH : 25000000 ≤ H) :
    exp (sqrt ((b / 6) / (m + 4 : ℕ))) ≤ H := by
  have hq : (4 : ℝ) ≤ (m + 4 : ℕ) := by exact_mod_cast (show 4 ≤ m + 4 by omega)
  have hqpos : (0 : ℝ) < (m + 4 : ℕ) := by linarith
  have hd : (b / 6) / (m + 4 : ℕ) ≤ (15 : ℝ) ^ 2 := by
    apply (div_le_iff₀ hqpos).mpr
    nlinarith
  have hs := sq_sqrt (show 0 ≤ (b / 6) / (m + 4 : ℕ) from
    div_nonneg (div_nonneg hb (by norm_num)) hqpos.le)
  have hn := sqrt_nonneg ((b / 6) / (m + 4 : ℕ))
  have hroot : sqrt ((b / 6) / (m + 4 : ℕ)) ≤ 15 := by nlinarith
  calc
    _ ≤ exp 15 := exp_le_exp.mpr hroot
    _ = exp (1 : ℝ) ^ 15 := by rw [← exp_nat_mul]; norm_num
    _ ≤ (3 : ℝ) ^ 15 := pow_le_pow_left₀ (exp_pos 1).le
      (by linarith [exp_one_lt_d9]) 15
    _ ≤ H := by norm_num at hH ⊢; linarith

/-- Rational endpoints and smoothing parameters suffice to describe a row. -/
structure DusartFrozenThetaRow where
  lower : ℚ
  upper : ℚ
  orderOffset : ℕ
  step : ℚ
  power : ℚ

namespace DusartFrozenThetaRow

/-- The complete relative theta allowance, including both averages and the root correction. -/
def budget (row : DusartFrozenThetaRow) (H : ℝ) : ℝ :=
  dusartFrozenLogPsiBound row.orderOffset row.step row.lower row.power H +
    (8 / 5) * exp (-(row.lower : ℝ) / 2)

/-- Rational row geometry is shared by the original and reflected scalar bounds. -/
structure Geometry (row : DusartFrozenThetaRow) : Prop where
  lower_ge : 25 ≤ row.lower
  ordered : row.lower ≤ row.upper
  upper_le : row.upper ≤ 5000
  step_pos : 0 < row.step
  step_small : (row.orderOffset + 3 : ℕ) * row.step ≤ (1 / 2 : ℚ)
  power_gt : 1 < row.power
  power_lt : row.power < (row.orderOffset + 4 : ℕ)

/-- Scalar validity adds the original budget cap to the shared row geometry. -/
structure Valid (row : DusartFrozenThetaRow) (H : ℝ) : Prop extends Geometry row where
  cap : row.budget H * (row.upper : ℝ) ^ 2 ≤ (1 / 5 : ℝ)

/-- Row geometry alone keeps the shifted logarithm on the safe positive ray. -/
theorem shift_geometry {row : DusartFrozenThetaRow} (hlower : 25 ≤ row.lower)
    (hstep : (row.orderOffset + 3 : ℕ) * row.step ≤ (1 / 2 : ℚ)) :
    0 < 1 - (row.orderOffset + 3 : ℕ) * (row.step : ℝ) ∧
    1 ≤ (row.lower : ℝ) + log (1 - (row.orderOffset + 3 : ℕ) * (row.step : ℝ)) := by
  have hlo : (25 : ℝ) ≤ row.lower := by exact_mod_cast hlower
  have hs : (row.orderOffset + 3 : ℕ) * (row.step : ℝ) ≤ (1 / 2 : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hstep
    push_cast at hc
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hc
  have ht : (1 / 2 : ℝ) ≤ 1 - (row.orderOffset + 3 : ℕ) * (row.step : ℝ) := by linarith
  have hl := log_le_log (by norm_num : (0 : ℝ) < 1 / 2) ht
  rw [log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), log_one] at hl
  constructor <;> linarith [log_two_lt_d9]

/-- Every valid row has the shifted geometry required by the analytic bound. -/
theorem Valid.shift {row : DusartFrozenThetaRow} {H : ℝ} (h : row.Valid H) :
    0 < 1 - (row.orderOffset + 3 : ℕ) * (row.step : ℝ) ∧
    1 ≤ (row.lower : ℝ) + log (1 - (row.orderOffset + 3 : ℕ) * (row.step : ℝ)) :=
  shift_geometry h.lower_ge h.step_small

/-- Any proved psi allowance converts to theta using the same sharper root correction. -/
theorem Geometry.theta_bound {row : DusartFrozenThetaRow} {B x : ℝ} (h : row.Geometry)
    (hxpos : 0 < x) (hxlo : (row.lower : ℝ) ≤ log x) (hxhi : log x ≤ row.upper)
    (hpsi : |Chebyshev.psi x - x| / x ≤ B)
    (hcap : (B + (8 / 5) * exp (-(row.lower : ℝ) / 2)) * (row.upper : ℝ) ^ 2 ≤ 1 / 5) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  have hb : (25 : ℝ) ≤ row.lower := by exact_mod_cast h.lower_ge
  have hxbase : exp (row.lower : ℝ) ≤ x := by
    simpa only [exp_log hxpos] using exp_le_exp.mpr hxlo
  have hxthree : (3000000000 : ℝ) ≤ x := dusartFrozen_exp_twentyFive_ge.trans
    ((exp_le_exp.mpr hb).trans hxbase)
  have hsquare : exp ((row.lower : ℝ) / 2) ^ 2 ≤ x := by
    calc
      _ = exp ((row.lower : ℝ) / 2 + (row.lower : ℝ) / 2) := by rw [pow_two, exp_add]
      _ = exp (row.lower : ℝ) := by congr 1; ring
      _ ≤ x := hxbase
  have htheta := abs_theta_sub_div_le_sharper_root hxthree
    (exp_pos ((row.lower : ℝ) / 2)) hsquare hpsi
  have htheta' : |Chebyshev.theta x - x| / x ≤ B + (8 / 5) * exp (-(row.lower : ℝ) / 2) := by
    simpa only [show -(row.lower : ℝ) / 2 = -((row.lower : ℝ) / 2) by ring,
      exp_neg, div_eq_mul_inv] using htheta
  exact abs_theta_sub_le_logSquared_of_earlier_cap (by linarith) hxhi hcap htheta'

/-- A valid scalar row proves the exact theta bound throughout its logarithmic interval. -/
theorem Valid.bound {row : DusartFrozenThetaRow} {H x : ℝ} (h : row.Valid H)
    (hH : 25000000 ≤ H) (hH₁ : H ≤ 1000000000)
    (hlow : ∀ z ∈ xiLowHeightIndices H,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤ 1 - 1 / (6 * log |(riemannXiDivisorZeroValue z).im|))
    (hxpos : 0 < x) (hxlo : (row.lower : ℝ) ≤ log x) (hxhi : log x ≤ row.upper) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  let b : ℝ := row.lower
  let s : ℝ := row.step
  let t : ℝ := 1 - (row.orderOffset + 3 : ℕ) * s
  have hb : 25 ≤ b := by dsimp [b]; exact_mod_cast h.lower_ge
  have hb₁ : b ≤ 5000 := by dsimp [b]; exact_mod_cast h.ordered.trans h.upper_le
  have hs : 0 < s := by dsimp [s]; exact_mod_cast h.step_pos
  have hp : (1 : ℝ) < row.power := by exact_mod_cast h.power_gt
  have hpq : (row.power : ℝ) < (row.orderOffset + 4 : ℕ) := by exact_mod_cast h.power_lt
  obtain ⟨ht, hlog⟩ := h.shift
  have htpos : 0 < t := ht
  have he : log (exp b * t) = b + log t := by
    rw [log_mul (exp_pos b).ne' htpos.ne', log_exp]
  have hy : 1 < exp b * t := by
    have ha := add_one_le_exp (log (exp b * t))
    rw [exp_log (mul_pos (exp_pos b) htpos), he] at ha
    change 1 ≤ b + log t at hlog
    linarith
  have hxbase : exp b ≤ x := by simpa only [exp_log hxpos] using exp_le_exp.mpr hxlo
  have hpeak : exp (sqrt ((log (exp b) / 6) / (row.orderOffset + 4 : ℕ))) ≤ H := by
    rw [log_exp]
    exact dusartFrozen_peak_le row.orderOffset (by linarith) hb₁ hH
  have hpsi := abs_psi_sub_div_le_frozen row.orderOffset hs (exp_pos b) hxbase hy
    (by norm_num : (0 : ℝ) < 6) hp hpq (by norm_num : (10 : ℝ) ≤ 10)
    (by linarith : (10 : ℝ) < H) (by norm_num : (0 : ℝ) < 1 / 2)
    (by simpa only [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] using hlow) hpeak hreg
  have hbudget := dusartRosserFrozenPsiBound_le_logPeak row.orderOffset hs
    (by linarith : 1 ≤ b) ht hlog hp hpq (by linarith : 10 ≤ H) hH₁
  exact h.toGeometry.theta_bound hxpos hxlo hxhi (hpsi.trans hbudget) h.cap

end DusartFrozenThetaRow

end

end PrimeFactorUnimodality
