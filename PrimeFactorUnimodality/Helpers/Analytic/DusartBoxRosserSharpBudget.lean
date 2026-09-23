import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserNuBudget
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserSharpComparison

/-! # Actual psi estimates with the sharp Rosser density tail

The finite band and low-prefix estimates are reused. Only the density
tail is sharpened using the upper primitive. The Lemma 49 parameter
condition is explicit, and is transported to the larger adjacent average
by monotonicity. No numerical zero-free region is assumed implicitly.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

/-- The complete elementary error budget using the sharp density-tail coefficient. -/
def dusartBoxRosserSharpErrorBudget (m : ℕ) (h x R ν a H δ : ℝ) : ℝ :=
  let X := sqrt (Real.log x / R)
  ((x + (m + 3 : ℕ) * h) * exp (-δ * Real.log x)) * xiLowReciprocalNormBound a H δ +
    (x + (m + 3 : ℕ) * h) * (2 * xiRosserNuWindowBound X ν) +
    (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
      xiRosserSharpTailBound X (m + 3 : ℕ) ν + 1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)

/-- The complete sharp budget improves the previous elementary budget with identical parameters. -/
theorem dusartBoxRosserSharpErrorBudget_le_nu (m : ℕ) {h x R ν a H δ : ℝ}
    (hh : 0 < h) (hx : 0 < x) (hν : 0 < ν) (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2) :
    dusartBoxRosserSharpErrorBudget m h x R ν a H δ ≤
      dusartBoxRosserNuErrorBudget m h x R ν a H δ := by
  have ht := xiRosserSharpTailBound_le_nu (X := sqrt (Real.log x / R)) hν hmargin
  have hq : ((m + 3 : ℕ) : ℝ) + 1 = (m + 4 : ℕ) := by push_cast; ring
  rw [hq] at ht
  unfold dusartBoxRosserSharpErrorBudget dusartBoxRosserNuErrorBudget
  exact add_le_add (add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left ht (by positivity))) le_rfl) le_rfl

/-- The actual high-zero box sum inherits the sharp bound from the existing integral estimate. -/
theorem norm_dusartBoxXiHighSum_le_rosserSharp (m : ℕ) {h x R ν : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hν : 0 < ν)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (hparam : Real.log (2 * π) ≤
      1 / (m + 3 : ℕ) + sqrt ((Real.log x / R) / (m + 3 : ℕ)))
    (hT : 10 < exp (ν * sqrt (Real.log x / R)))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex,
      exp (ν * sqrt (Real.log x / R)) ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    ‖dusartBoxXiHighSum m h x (exp (ν * sqrt (Real.log x / R)))‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        xiRosserSharpTailBound (sqrt (Real.log x / R)) (m + 3 : ℕ) ν := by
  let X := sqrt (Real.log x / R)
  have hX : 0 < X := sqrt_pos.mpr (div_pos (Real.log_pos hx) hR)
  have hXsq : X ^ 2 = Real.log x / R := sq_sqrt (div_nonneg (Real.log_pos hx).le hR.le)
  have hq : ((m + 3 : ℕ) : ℝ) + 1 = (m + 4 : ℕ) := by push_cast; ring
  have hm : (1 : ℝ) ≤ (m + 3 : ℕ) := by norm_cast; omega
  have hmarg : 1 < (((m + 4 : ℕ) : ℝ) - 1) * ν ^ 2 := by
    rw [← hq, add_sub_cancel_right]
    exact hmargin
  have hdec : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ exp (ν * X) := by
    rw [← hXsq]
    exact logDampedPower_nu_turn_le hX hν hmarg
  have hs := xiRosserTailIntegral_boundary_le_sharp hX hm hν hmargin
    (by simpa only [hXsq] using hparam) hT
  rw [hXsq, hq] at hs
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  exact (norm_dusartBoxXiHighSum_le_rosserTail m hh hx hR hT hdec hreg).trans
    (mul_le_mul_of_nonneg_left hs (by positivity))

/-- The actual average combines the existing prefix and band with the sharper high tail. -/
theorem abs_dusartPsiAverageError_le_rosserSharpBudget (m : ℕ) {h x R ν a H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (hparam : Real.log (2 * π) ≤
      1 / (m + 3 : ℕ) + sqrt ((Real.log x / R) / (m + 3 : ℕ)))
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hδ : 0 < δ)
    (hHT : H ≤ exp (ν * sqrt (Real.log x / R)))
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxRosserSharpErrorBudget m h x R ν a H δ := by
  let X := sqrt (Real.log x / R)
  have hX : 0 < X := sqrt_pos.mpr (div_pos (Real.log_pos hx) hR)
  have hXsq : X ^ 2 = Real.log x / R := sq_sqrt (div_nonneg (Real.log_pos hx).le hR.le)
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlo := (norm_sum_dusartBox_xi_power_average_le m hh hx hδ.le
    (xiLowHeightIndices H) hgap).trans (mul_le_mul_of_nonneg_left
      (sum_xi_low_reciprocal_norm_le_explicit ha haH hδ hgap) (by positivity))
  have hinc : exp (ν * X) ≤ exp (sqrt (Real.log x / R)) :=
    exp_le_exp.mpr (by change ν * X ≤ X; nlinarith)
  have hb := xiRosserIncreasingBandBound_le_nu hX hν hH hHT
  rw [hXsq] at hb
  have hmid := (norm_dusartBox_band_le_rosser_increasing m hh hx hR hH hHT hinc
    (fun z hz => hreg z ((mem_xiHeightBandIndices H (exp (ν * X)) z).mp hz).1)).trans
      (mul_le_mul_of_nonneg_left hb (by positivity))
  have hhi := norm_dusartBoxXiHighSum_le_rosserSharp m hh hx hR hν hmargin hparam
    (by linarith) (fun z hz => hreg z (hHT.trans hz))
  have hs := (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hlo hmid)) hhi)
  rw [← smoothedXiPairedSum_box_eq_low_add_band_add_high m hh hx hHT] at hs
  exact (abs_dusartPsiAverageError_le_zero_sum m hh hx).trans
    (add_le_add (add_le_add hs le_rfl) le_rfl)

/-- Adjacent averages use their own cutoffs; the sharp parameter condition propagates upwards. -/
theorem abs_psi_sub_le_dusartBoxRosserSharpBudget (m : ℕ) {h x R ν a H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (hR : 0 < R)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (hparam : Real.log (2 * π) ≤ 1 / (m + 3 : ℕ) +
      sqrt ((Real.log (x - (m + 3 : ℕ) * h) / R) / (m + 3 : ℕ)))
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hδ : 0 < δ)
    (hHT : H ≤ exp (ν * sqrt (Real.log (x - (m + 3 : ℕ) * h) / R)))
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| ≤
      max (dusartBoxRosserSharpErrorBudget m h (x - (m + 3 : ℕ) * h) R ν a H δ)
        (dusartBoxRosserSharpErrorBudget m h x R ν a H δ) + (m + 3 : ℕ) * h / 2 := by
  have hleft : x - (m + 3 : ℕ) * h ≤ x :=
    sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hh.le)
  have hx' : 1 < x := hx.trans_le hleft
  have hlog := div_le_div_of_nonneg_right
    (Real.log_le_log (lt_trans zero_lt_one hx) hleft) hR.le
  have hHT' := hHT.trans (exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hlog) hν.le))
  have hparam' := hparam.trans (add_le_add le_rfl
    (sqrt_le_sqrt (div_le_div_of_nonneg_right hlog (Nat.cast_nonneg _))))
  exact dusart_abs_psi_error_le_of_averages (m + 3) hh
    ((abs_dusartPsiAverageError_le_rosserSharpBudget m hh hx hR hν hν1 hmargin hparam
      ha haH hH hδ hHT hgap hreg).trans (le_max_left _ _))
    ((abs_dusartPsiAverageError_le_rosserSharpBudget m hh hx' hR hν hν1 hmargin hparam'
      ha haH hH hδ hHT' hgap hreg).trans (le_max_right _ _))

end

end PrimeFactorUnimodality
