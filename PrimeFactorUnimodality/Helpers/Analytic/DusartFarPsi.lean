import PrimeFactorUnimodality.Helpers.Analytic.DusartFarShift
import PrimeFactorUnimodality.Helpers.Analytic.DusartPsiRelativeAverages

/-! # Actual pointwise square-log psi error on the far ray

Apply the evaluated average to both base points, each with its own root
parameter and normalization. The shift costs at most a factor four in
the reciprocal log square; smoothing fits in the remaining hundredth.
The conclusion includes every point, including prime-power jumps.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The actual pointwise psi error is at most one twentieth of the log-square scale. -/
theorem abs_psi_sub_div_le_far {x : ℝ} (hx : 1 < x) (hb : 5000 ≤ Real.log x)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |Chebyshev.psi x - x| / x ≤ (1 / 20 : ℝ) / Real.log x ^ 2 := by
  let b := Real.log x
  let s := exp (-(4 / 5 : ℝ) * sqrt (b / 6))
  let t := 1 - 3 * s
  have hbpos : 0 < b := Real.log_pos hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hspos : 0 < s := exp_pos _
  obtain ⟨ht, ht1, hy1, hbl, _⟩ := dusartFar_shift_geometry hx hb
  have htpos : 0 < t := by dsimp [t, s, b]; linarith
  have hypos : 0 < x * t := mul_pos hxpos htpos
  have hbl4704 : 4704 ≤ Real.log (x * t) := by linarith
  have hblhalf : b / 2 ≤ Real.log (x * t) := by dsimp [b]; linarith
  obtain ⟨hleftlo, hlefthi⟩ := dusartFar_left_step_window hx hb
  have hleft := abs_dusartPsiAverageError_div_le_far hy1 hbl4704 hleftlo hlefthi hgap hreg
  have hstep : (s / t) * (x * t) = s * x := by field_simp
  change |dusartPsiAverageError 3 ((s / t) * (x * t)) (x * t)| / (x * t) ≤ _ at hleft
  rw [hstep] at hleft
  have hright := abs_dusartPsiAverageError_div_le_far hx (by linarith : 4704 ≤ Real.log x)
    (by dsimp [s, b]; linarith [exp_pos (-(4 / 5 : ℝ) * sqrt (b / 6))] :
      exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6)) / 2 ≤ s)
    (by dsimp [s, b]; linarith [exp_pos (-(4 / 5 : ℝ) * sqrt (b / 6))] :
      s ≤ 2 * exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6))) hgap hreg
  have hp := dusart_abs_psi_div_le_of_relative_averages 3 hspos hxpos hypos hleft hright
  have hleftcap : t * ((1 / 100 : ℝ) / Real.log (x * t) ^ 2) ≤ (1 / 25 : ℝ) / b ^ 2 := by
    calc
      _ ≤ (1 / 100 : ℝ) / Real.log (x * t) ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1
          (by positivity : 0 ≤ (1 / 100 : ℝ) / Real.log (x * t) ^ 2)
      _ ≤ (1 / 100 : ℝ) / (b / 2) ^ 2 := div_le_div_of_nonneg_left (by norm_num)
        (by positivity) (pow_le_pow_left₀ (by positivity) hblhalf 2)
      _ = _ := by field_simp; ring
  have hrightcap : (1 / 100 : ℝ) / b ^ 2 ≤ (1 / 25 : ℝ) / b ^ 2 :=
    div_le_div_of_nonneg_right (by norm_num) (sq_nonneg b)
  have hsmooth : 3 * s / 2 ≤ (1 / 100 : ℝ) / b ^ 2 := by
    have hm := dusartFar_smoothing_moment_le (dusartFar_root_ge (by linarith : 4704 ≤ b))
    have hscale : b ^ 2 = 36 * sqrt (b / 6) ^ 4 := by
      have hsquare := sq_sqrt (by positivity : 0 ≤ b / 6)
      calc
        _ = (6 * sqrt (b / 6) ^ 2) ^ 2 := by congr 1; linarith
        _ = _ := by ring
    rw [← hscale] at hm
    apply (le_div_iff₀ (pow_pos hbpos 2)).mpr
    nlinarith only [hm]
  calc
    _ ≤ max (t * ((1 / 100 : ℝ) / Real.log (x * t) ^ 2))
        ((1 / 100 : ℝ) / b ^ 2) + 3 * s / 2 := hp
    _ ≤ (1 / 25 : ℝ) / b ^ 2 + (1 / 100 : ℝ) / b ^ 2 :=
      add_le_add (max_le hleftcap hrightcap) hsmooth
    _ = _ := by dsimp [b]; ring

end

end PrimeFactorUnimodality
