import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxOscillation
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPowerTail
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPsiError
import PrimeFactorUnimodality.Helpers.Analytic.DusartPsiRelativeAverages

/-! # Cancellation-preserving psi bounds from low-zero phase estimates

Only the already separated high tail uses termwise absolute values. A bound
on the entire finite phase sum supplies the low contribution. Both adjacent
averages are included, with the left relative width adjusted exactly.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex intervalIntegral

/-- A complete normalized average budget, with the signed low sum bounded by `B`. -/
def dusartBoxPhaseBudget (m : ℕ) (s x T B : ℝ) : ℝ :=
  Real.exp (-Real.log x / 2) * B +
    (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
      xiRosserPowerTailBound (m + 4 : ℕ) T +
    (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * Real.pi)) / x

/-- A numerical bound on the actual low phase sum controls the actual averaged psi error. -/
theorem abs_dusartPsiAverageError_div_le_phase (m : ℕ) {s x T B : ℝ} (u : ℝ)
    (hs : 0 < s) (hx : 1 < x) (hT : 10 < T)
    (hline : ∀ z ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue z).re = 1 / 2)
    (hphase : ‖dusartBoxLowPhaseSum m s u T (Real.log x - u)‖ ≤ B) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤ dusartBoxPhaseBudget m s x T B := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlow := mul_le_mul_of_nonneg_left hphase (Real.exp_pos (-Real.log x / 2)).le
  rw [← norm_dusartBox_low_div_eq_phase m u hs hxpos hline] at hlow
  have hhigh := norm_dusartBoxXiHighSum_div_le_power m hs hx hT
  have hmain := div_le_div_of_nonneg_right
    (abs_dusartPsiAverageError_le_zero_sum m (mul_pos hs hxpos) hx) hxpos.le
  rw [smoothedXiPairedSum_box_eq_low_add_high m (mul_pos hs hxpos) hx T] at hmain
  have hsum := div_le_div_of_nonneg_right (norm_add_le
    (∑ z ∈ xiLowHeightIndices T, iteratedBoxAverageComplex (s * x) (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x)
    (dusartBoxXiHighSum m (s * x) x T)) hxpos.le
  rw [add_div] at hsum
  refine hmain.trans ?_
  rw [show (‖(∑ z ∈ xiLowHeightIndices T, iteratedBoxAverageComplex (s * x) (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x) +
      dusartBoxXiHighSum m (s * x) x T‖ + 1 / (2 * (x ^ 2 - 1)) +
      Real.log (2 * Real.pi)) / x =
      ‖(∑ z ∈ xiLowHeightIndices T, iteratedBoxAverageComplex (s * x) (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x) +
        dusartBoxXiHighSum m (s * x) x T‖ / x +
        (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * Real.pi)) / x by ring]
  exact add_le_add (hsum.trans (add_le_add hlow hhigh)) le_rfl

/-- Two independently bounded phase sums give a pointwise bound, including prime-power jumps. -/
theorem dusart_abs_psi_div_le_phase (m : ℕ) {s x T L U : ℝ} (u v : ℝ)
    (hs : 0 < s) (hx : 1 < x) (hT : 10 < T)
    (hq : 0 < 1 - (m + 3 : ℕ) * s) (hy : 1 < x * (1 - (m + 3 : ℕ) * s))
    (hline : ∀ z ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue z).re = 1 / 2)
    (hleft : ‖dusartBoxLowPhaseSum m (s / (1 - (m + 3 : ℕ) * s)) u T
      (Real.log (x * (1 - (m + 3 : ℕ) * s)) - u)‖ ≤ L)
    (hright : ‖dusartBoxLowPhaseSum m s v T (Real.log x - v)‖ ≤ U) :
    |Chebyshev.psi x - x| / x ≤
      max ((1 - (m + 3 : ℕ) * s) *
        dusartBoxPhaseBudget m (s / (1 - (m + 3 : ℕ) * s))
          (x * (1 - (m + 3 : ℕ) * s)) T L)
        (dusartBoxPhaseBudget m s x T U) + (m + 3 : ℕ) * s / 2 := by
  have hl := abs_dusartPsiAverageError_div_le_phase m u (div_pos hs hq) hy hT hline hleft
  have he : s / (1 - (m + 3 : ℕ) * s) * (x * (1 - (m + 3 : ℕ) * s)) = s * x := by
    calc
      _ = (s * x / (1 - (m + 3 : ℕ) * s)) * (1 - (m + 3 : ℕ) * s) := by ring
      _ = _ := div_mul_cancel₀ _ hq.ne'
  rw [he] at hl
  exact dusart_abs_psi_div_le_of_relative_averages (m + 3) hs (zero_lt_one.trans hx)
    (zero_lt_one.trans hy) hl (abs_dusartPsiAverageError_div_le_phase m v hs hx hT hline hright)

end

end PrimeFactorUnimodality
