import PrimeFactorUnimodality.Helpers.Analytic.DusartMiddleShift
import PrimeFactorUnimodality.Helpers.Analytic.DusartPsiRelativeAverages

/-! # Actual pointwise square-log psi error through the middle range

Both adjacent averages use the evaluated step window at their actual
base points. The lower logarithm changes its error by less than the
reserved allowance; the chosen smoothing cost is exactly 0.12/log(x)^2.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Actual adjacent averages give the pointwise middle-range bound, including jumps. -/
theorem abs_psi_sub_div_le_middle {x : ℝ}
    (hx : 1 < x) (hb : 85 ≤ Real.log x) (hb₁ : Real.log x ≤ 5000)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |Chebyshev.psi x - x| / x ≤ (19 / 100 : ℝ) / Real.log x ^ 2 := by
  let b := Real.log x
  let s := (2 / 25 : ℝ) / b ^ 2
  let t := 1 - 3 * s
  have hbpos : 0 < b := Real.log_pos hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hspos : 0 < s := by dsimp [s]; positivity
  obtain ⟨ht, ht1, hy1, hbl, hbu⟩ := dusartMiddle_shift_geometry hx hb
  have htpos : 0 < t := by dsimp [t, s, b]; linarith
  have hypos : 0 < x * t := mul_pos hxpos htpos
  have hcpos : 0 < Real.log (x * t) := Real.log_pos hy1
  have hbl84 : 84 ≤ Real.log (x * t) := by linarith
  have hbu5000 : Real.log (x * t) ≤ 5000 := hbu.trans hb₁
  have hratio : (49 / 50 : ℝ) * b ≤ Real.log (x * t) := by dsimp [b]; linarith
  obtain ⟨hleftlo, hlefthi⟩ := dusartMiddle_left_step_window hx hb
  have hleft := abs_dusartPsiAverageError_div_le_middle hy1 hbl84 hbu5000
    hleftlo hlefthi hgap hreg
  have hstep : (s / t) * (x * t) = s * x := by field_simp
  change |dusartPsiAverageError 3 ((s / t) * (x * t)) (x * t)| / (x * t) ≤ _ at hleft
  rw [hstep] at hleft
  have hright := abs_dusartPsiAverageError_div_le_middle hx (by linarith : 84 ≤ Real.log x) hb₁
    (div_le_div_of_nonneg_right (by norm_num : (3 / 40 : ℝ) ≤ 2 / 25) (sq_nonneg b))
    (div_le_div_of_nonneg_right (by norm_num : (2 / 25 : ℝ) ≤ 17 / 200) (sq_nonneg b)) hgap hreg
  have hp := dusart_abs_psi_div_le_of_relative_averages 3 hspos hxpos hypos hleft hright
  have hleftcap : t * ((3 / 50 : ℝ) / Real.log (x * t) ^ 2) ≤ (7 / 100 : ℝ) / b ^ 2 := by
    calc
      _ ≤ (3 / 50 : ℝ) / Real.log (x * t) ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1
          (by positivity : 0 ≤ (3 / 50 : ℝ) / Real.log (x * t) ^ 2)
      _ ≤ _ := by
        apply (div_le_div_iff₀ (pow_pos hcpos 2) (pow_pos hbpos 2)).mpr
        have hsq := pow_le_pow_left₀ (by positivity) hratio 2
        nlinarith only [hsq, sq_nonneg b]
  have hrightcap : (3 / 50 : ℝ) / b ^ 2 ≤ (7 / 100 : ℝ) / b ^ 2 :=
    div_le_div_of_nonneg_right (by norm_num) (sq_nonneg b)
  calc
    _ ≤ max (t * ((3 / 50 : ℝ) / Real.log (x * t) ^ 2))
        ((3 / 50 : ℝ) / b ^ 2) + 3 * s / 2 := hp
    _ ≤ (7 / 100 : ℝ) / b ^ 2 + 3 * s / 2 :=
      add_le_add (max_le hleftcap hrightcap) le_rfl
    _ = _ := by dsimp [s, b]; ring

end

end PrimeFactorUnimodality
