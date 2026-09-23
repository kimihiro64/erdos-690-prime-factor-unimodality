import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxHeightGap
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserWindow

/-! # Rosser counting bounds for the actual higher-order box atoms

The full inverse-height power is retained in the damped kernel, instead
of reducing it to an inverse square at the lower cutoff. A region with
arbitrary positive constant `R` gives the kernel parameters `log(x)/R`
and `m+4`. The initial constant `56` is then supplied by the proved region.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real intervalIntegral

/-- Either ordinate sign has the same full damped-power bound at its absolute height. -/
theorem norm_dusartBox_atom_le_abs_rosser_kernel (m : ℕ) {h x R : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) {s : ℂ} (hγ : 1 < |s.im|)
    (hβ0 : 0 ≤ s.re) (hβ : s.re ≤ 1 - 1 / (R * Real.log |s.im|)) :
    ‖iteratedBoxAverageComplex h (m + 3) (fun t => (t : ℂ) ^ s / s) x‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        logDampedPower (Real.log x / R) (m + 4 : ℕ) |s.im| := by
  have hγ0 : 0 < |s.im| := lt_trans zero_lt_one hγ
  have hs : s ≠ 0 := fun he => (abs_pos.mp hγ0) (by simp [he])
  have hδ : 0 ≤ 1 / (R * Real.log |s.im|) :=
    one_div_nonneg.mpr (mul_nonneg hR.le (Real.log_pos hγ).le)
  have hb := norm_dusartBox_paired_atom_le_height_gap m hh hx hδ (abs_pos.mp hγ0) hβ0 hβ
  rw [finiteLaplace_dusartBoxWeight_add_inv m hh hx hs] at hb
  refine hb.trans_eq ?_
  rw [logDampedPower_eq_rpow_mul hγ0, Real.rpow_neg hγ0.le, Real.rpow_natCast]
  have he : -(1 / (R * Real.log |s.im|)) * Real.log x =
      -(Real.log x / R) / Real.log |s.im| := by ring
  rw [he]
  ring

/-- The positive-height interface specializes the same absolute-height atom estimate. -/
theorem norm_dusartBox_atom_le_rosser_kernel (m : ℕ) {h x R : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) {s : ℂ} (hγ : 1 < s.im)
    (hβ0 : 0 ≤ s.re) (hβ : s.re ≤ 1 - 1 / (R * Real.log s.im)) :
    ‖iteratedBoxAverageComplex h (m + 3) (fun t => (t : ℂ) ^ s / s) x‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        logDampedPower (Real.log x / R) (m + 4 : ℕ) s.im := by
  have he : |s.im| = s.im := abs_of_pos (lt_trans zero_lt_one hγ)
  simpa only [he] using norm_dusartBox_atom_le_abs_rosser_kernel m hh hx hR
    (by simpa only [he] using hγ) hβ0 (by simpa only [he] using hβ)

/-- The actual finite spectral sum is bounded by the explicit Rosser integral expression. -/
theorem norm_dusartBox_xi_window_le_rosser (m : ℕ) {h x R u v : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hu : 10 ≤ u) (huv : u ≤ v)
    (hreg : ∀ p ∈ xiHeightWindowIndices u v,
      (riemannXiDivisorZeroValue p).re ≤
        1 - 1 / (R * Real.log (riemannXiDivisorZeroValue p).im)) :
    ‖∑ p ∈ xiHeightWindowIndices u v, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        xiRosserWindowBound (Real.log x / R) (m + 4 : ℕ) u v := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ p ∈ xiHeightWindowIndices u v,
        (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
          logDampedPower (Real.log x / R) (m + 4 : ℕ) (riemannXiDivisorZeroValue p).im := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := (mem_xiHeightWindowIndices u v p).mp hp
      exact norm_dusartBox_atom_le_rosser_kernel m hh hx hR (by linarith [hp'.2])
        (riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)).1 (hreg p hp)
    _ = _ * ∑ p ∈ xiHeightWindowIndices u v,
        logDampedPower (Real.log x / R) (m + 4 : ℕ) (riemannXiDivisorZeroValue p).im := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_xi_logDampedPower_le (div_nonneg (Real.log_pos hx).le hR.le)
        (by positivity) hu huv) (by positivity)

/-- Above the initial cutoff no region hypothesis is needed for the actual zero sum. -/
theorem norm_dusartBox_xi_window_le_initial_rosser (m : ℕ) {h x u v : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hu : 10 ^ 9 ≤ u) (huv : u ≤ v) :
    ‖∑ p ∈ xiHeightWindowIndices u v, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        xiRosserWindowBound (Real.log x / 56) (m + 4 : ℕ) u v := by
  apply norm_dusartBox_xi_window_le_rosser m hh hx (by norm_num) (by linarith) huv
  intro p hp
  have hp' := (mem_xiHeightWindowIndices u v p).mp hp
  have ht : 10 ^ 9 ≤ |(riemannXiDivisorZeroValue p).im| := by
    rw [abs_of_pos hp'.1.1]
    exact hu.trans hp'.2.le
  have hz := xi_zero_gap_initial (riemannXiDivisorZeroValue_eq_zero p) ht
  rw [abs_of_pos hp'.1.1] at hz
  linarith

end

end PrimeFactorUnimodality
