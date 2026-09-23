import PrimeFactorUnimodality.Helpers.Analytic.DusartLogarithmicAverage
import PrimeFactorUnimodality.Helpers.Analytic.DusartPsiRelativeAverages

/-! # Pointwise psi error decreasing as the reciprocal logarithm

Choose a relative step inversely proportional to the logarithm. Both
adjacent averages lie in the proved step window, including the shifted
base point and its different normalization. The actual psi estimate
includes prime-power jumps and holds on the entire logarithmic ray.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Explicit adjacent averages give the actual pointwise logarithmic error. -/
theorem abs_psi_sub_div_le_logarithmic_of_billion_low_gap {x : ℝ}
    (hx : 1 < x) (hb : 100 ≤ Real.log x)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.psi x - x| / x ≤ (103 / 100 : ℝ) / Real.log x := by
  let b := Real.log x
  let s := 1 / (50 * b)
  let t := 1 - 3 * s
  have hbpos : 0 < b := Real.log_pos hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hspos : 0 < s := by dsimp [s]; positivity
  have hsmax : s ≤ (1 / 5000 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by dsimp [b]; linarith)
  have ht : (1 / 2 : ℝ) ≤ t := by dsimp [t]; linarith
  have htpos : 0 < t := by linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hypos : 0 < x * t := mul_pos hxpos htpos
  have hy1 : 1 < x * t := by
    have he := Real.add_one_le_exp b
    rw [Real.exp_log hxpos] at he
    have hm := mul_le_mul_of_nonneg_left ht hxpos.le
    dsimp [b] at he
    nlinarith
  have hylog : Real.log (x * t) = b + Real.log t := Real.log_mul hxpos.ne' htpos.ne'
  have hlogt : -1 ≤ Real.log t := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) ht
    rw [one_div, Real.log_inv] at hl
    linarith [Real.log_two_lt_d9]
  have hlogt1 : Real.log t ≤ 0 := Real.log_nonpos htpos.le ht1
  have hbl : b - 1 ≤ Real.log (x * t) := by linarith
  have hbu : Real.log (x * t) ≤ b := by linarith
  have hbl50 : 50 ≤ Real.log (x * t) := by dsimp [b] at hbl; linarith
  have hblhalf : b / 2 ≤ Real.log (x * t) := by dsimp [b] at hbl ⊢; linarith
  have hleftlo : 1 / (60 * Real.log (x * t)) ≤ s / t := by
    calc
      _ ≤ s := one_div_le_one_div_of_le (by positivity)
        (by dsimp [b] at hbl ⊢; linarith)
      _ ≤ s / t := (le_div_iff₀ htpos).mpr (by nlinarith)
  have hlefthi : s / t ≤ 1 / (20 * Real.log (x * t)) := by
    calc
      _ ≤ 2 * s := (div_le_iff₀ htpos).mpr (by nlinarith)
      _ = 1 / (25 * b) := by dsimp [s]; ring
      _ ≤ _ := one_div_le_one_div_of_le (by linarith)
        (by linarith)
  have hrightlo : 1 / (60 * b) ≤ s :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hrighthi : s ≤ 1 / (20 * b) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hleft := abs_dusartPsiAverageError_div_le_logarithmic hy1 hbl50
    hleftlo hlefthi hgap
  have hstep : (s / t) * (x * t) = s * x := by field_simp
  rw [hstep] at hleft
  have hright := abs_dusartPsiAverageError_div_le_logarithmic hx (by linarith)
    hrightlo hrighthi hgap
  have hp := dusart_abs_psi_div_le_of_relative_averages 3 hspos hxpos hypos hleft hright
  have hleftcap : t * (1 / (2 * Real.log (x * t))) ≤ 1 / b := by
    calc
      _ ≤ 1 / (2 * Real.log (x * t)) := by
        nlinarith [(one_div_pos.mpr (by linarith : 0 < 2 * Real.log (x * t)))]
      _ ≤ _ := one_div_le_one_div_of_le hbpos (by linarith)
  have hrightcap : 1 / (2 * b) ≤ 1 / b :=
    one_div_le_one_div_of_le hbpos (by linarith)
  calc
    _ ≤ max (t * (1 / (2 * Real.log (x * t)))) (1 / (2 * b)) + 3 * s / 2 := hp
    _ ≤ 1 / b + 3 * s / 2 := add_le_add (max_le hleftcap hrightcap) le_rfl
    _ = _ := by dsimp [s, b]; ring

end

end PrimeFactorUnimodality
