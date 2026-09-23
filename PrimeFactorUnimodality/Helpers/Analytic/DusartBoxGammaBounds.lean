import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPowerTransform
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedPairedSums

/-! # The complete negative-even correction for the Dusart box

Each paired Gamma atom is the average of its negative-even divided power.
On the positive averaging support these powers have a geometric majorant.
Summing it bounds the entire correction by `1 / (2 * (x^2 - 1))`, without
an unspecified derivative bound or omission of the low negative-even zeros.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real intervalIntegral

theorem norm_dusartBox_gamma_power_le {x t : ℝ} (hx : 1 < x) (ht : x ≤ t) (n : ℕ) :
    ‖(t : ℂ) ^ shiftedGammaPole n / shiftedGammaPole n‖ ≤
      ((x ^ 2)⁻¹) ^ (n + 1) / 2 := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hre : (shiftedGammaPole n).re = -(2 * ((n : ℝ) + 1)) := by
    simp [shiftedGammaPole]
  have hn : ‖shiftedGammaPole n‖ = 2 * ((n : ℝ) + 1) := by
    simp [shiftedGammaPole, norm_natCast_add_one]
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos (hx0.trans_le ht), hre, hn]
  have he : x ^ (-(2 * ((n : ℝ) + 1))) = ((x ^ 2)⁻¹) ^ (n + 1) := by
    rw [Real.rpow_neg hx0.le]
    have hc : 2 * ((n : ℝ) + 1) = ((2 * (n + 1) : ℕ) : ℝ) := by push_cast; ring
    rw [hc, Real.rpow_natCast, pow_mul, inv_pow]
  calc
    _ ≤ x ^ (-(2 * ((n : ℝ) + 1))) / (2 * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hx0 ht (neg_nonpos.mpr (by positivity))) (by positivity)
    _ = ((x ^ 2)⁻¹) ^ (n + 1) / (2 * ((n : ℝ) + 1)) := by rw [he]
    _ ≤ ((x ^ 2)⁻¹) ^ (n + 1) / 2 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num)
        (by have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)

theorem norm_dusartBox_gamma_average_le (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) (n : ℕ) :
    ‖iteratedBoxAverageComplex h (m + 3)
      (fun t => (t : ℂ) ^ shiftedGammaPole n / shiftedGammaPole n) x‖ ≤
        ((x ^ 2)⁻¹) ^ (n + 1) / 2 := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  exact norm_iteratedBoxAverageComplex_le_on_Ici hh
    ((continuousOn_ofReal_cpow_Ici hx0 (shiftedGammaPole n)).div_const _)
    le_rfl (m + 3) (fun t ht => norm_dusartBox_gamma_power_le hx ht.1 n)

/-- Every negative-even atom remains paired with its reciprocal constant. -/
theorem smoothedGammaPairedSum_box_eq_power_average (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) :
    smoothedGammaPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
      (dusartBoxSupport m h x) 0 =
      ∑' n : ℕ, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ shiftedGammaPole n / shiftedGammaPole n) x := by
  unfold smoothedGammaPairedSum
  apply tsum_congr
  intro n
  simp only [zero_sub, dusartBoxWeight_zero m hh hx.le, ofReal_one]
  exact finiteLaplace_dusartBoxWeight_add_inv m hh hx (shiftedGammaPole_ne_zero n)

/-- The explicit geometric series majorizing all the negative-even atoms. -/
theorem hasSum_dusartBox_gamma_majorant {x : ℝ} (hx : 1 < x) :
    HasSum (fun n : ℕ => ((x ^ 2)⁻¹) ^ (n + 1) / 2) (1 / (2 * (x ^ 2 - 1))) := by
  have hx2 : 1 < x ^ 2 := by nlinarith
  have hr0 : 0 < (x ^ 2)⁻¹ := inv_pos.mpr (by linarith)
  have hr1 : (x ^ 2)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hx2
  have hs := (hasSum_geometric_of_abs_lt_one
    (by rwa [abs_of_pos hr0] : |(x ^ 2)⁻¹| < 1)).mul_left ((x ^ 2)⁻¹ / 2)
  have hf : (fun n : ℕ => (x ^ 2)⁻¹ / 2 * ((x ^ 2)⁻¹) ^ n) =
      (fun n : ℕ => ((x ^ 2)⁻¹) ^ (n + 1) / 2) := by
    funext n
    rw [pow_succ]
    ring
  have he : (x ^ 2)⁻¹ / 2 * (1 - (x ^ 2)⁻¹)⁻¹ = 1 / (2 * (x ^ 2 - 1)) := by
    field_simp
  rwa [hf, he] at hs

/-- A uniform, explicit bound on the complete negative-even correction at zero. -/
theorem norm_smoothedGammaPairedSum_box_le (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) :
    ‖smoothedGammaPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
        (dusartBoxSupport m h x) 0‖ ≤ 1 / (2 * (x ^ 2 - 1)) := by
  have hB := hasSum_dusartBox_gamma_majorant hx
  have hnorm := Summable.of_nonneg_of_le
    (fun n => norm_nonneg (iteratedBoxAverageComplex h (m + 3)
      (fun t => (t : ℂ) ^ shiftedGammaPole n / shiftedGammaPole n) x))
    (norm_dusartBox_gamma_average_le m hh hx) hB.summable
  rw [smoothedGammaPairedSum_box_eq_power_average m hh hx]
  exact (norm_tsum_le_tsum_norm hnorm).trans
    ((hnorm.tsum_le_tsum (norm_dusartBox_gamma_average_le m hh hx) hB.summable).trans_eq hB.tsum_eq)

end

end PrimeFactorUnimodality
