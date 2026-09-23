import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserFixedRelative
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserFrozenTail

/-! # A starting-point bound for every later normalized psi average

Freeze the high-zero estimate at the starting point, then prove that the
normalized low-zero and correction terms decrease. Thus one evaluation of
the elementary budget controls every later average with the same relative
step. No new turning-point checks are required along the ray. The actual
zero-location hypotheses remain explicit.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real intervalIntegral

/-- The normalized negative-even and endpoint corrections decrease above one. -/
theorem dusartBox_relative_correction_le {x₀ x : ℝ} (hx₀ : 1 < x₀) (hx : x₀ ≤ x) :
    (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x ≤
      (1 / (2 * (x₀ ^ 2 - 1)) + Real.log (2 * π)) / x₀ := by
  have hx₀pos : 0 < x₀ := lt_trans zero_lt_one hx₀
  have hxpos : 0 < x := hx₀pos.trans_le hx
  have hd : 0 < 2 * (x₀ ^ 2 - 1) := by nlinarith
  have hdd : 2 * (x₀ ^ 2 - 1) ≤ 2 * (x ^ 2 - 1) := by nlinarith
  have hr := one_div_le_one_div_of_le hd hdd
  have hlog : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  calc
    _ ≤ (1 / (2 * (x₀ ^ 2 - 1)) + Real.log (2 * π)) / x :=
      div_le_div_of_nonneg_right (add_le_add hr le_rfl) hxpos.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hx₀pos hx

/-- The actual normalized low-zero block is controlled at the starting point. -/
theorem norm_dusartBox_low_div_le_frozen (m : ℕ) {s x x₀ a H δ : ℝ}
    (hs : 0 < s) (hx₀ : 1 < x₀) (hx : x₀ ≤ x)
    (ha : 10 ≤ a) (haH : a < H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ) :
    ‖∑ z ∈ xiLowHeightIndices H, iteratedBoxAverageComplex (s * x) (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x‖ / x ≤
      ((1 + (m + 3 : ℕ) * s) * exp (-δ * Real.log x₀)) *
        xiLowReciprocalNormBound a H δ := by
  have hx1 : 1 < x := hx₀.trans_le hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx1
  have hmass := sum_xi_low_reciprocal_norm_le_explicit ha haH hδ hgap
  have hM : 0 ≤ xiLowReciprocalNormBound a H δ :=
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hmass
  have hlow := (norm_sum_dusartBox_xi_power_average_le m (mul_pos hs hxpos) hx1
    hδ.le (xiLowHeightIndices H) hgap).trans
      (mul_le_mul_of_nonneg_left hmass (by positivity))
  have hd : exp (-δ * Real.log x) ≤ exp (-δ * Real.log x₀) := by
    apply Real.exp_le_exp.mpr
    have hlog := mul_le_mul_of_nonneg_left
      (Real.log_le_log (lt_trans zero_lt_one hx₀) hx) hδ.le
    linarith only [hlog]
  apply (div_le_iff₀ hxpos).mpr
  exact hlow.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hd (by positivity)) hM).trans_eq (by ring))

/-- A single elementary starting-point value bounds every later actual psi average. -/
theorem abs_dusartPsiAverageError_div_le_frozen (m : ℕ) {s x x₀ R p a H δ : ℝ}
    (hs : 0 < s) (hx₀ : 1 < x₀) (hx : x₀ ≤ x) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxRosserFixedRelativeBudget m s x₀ R p a H δ := by
  have hx1 : 1 < x := hx₀.trans_le hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx1
  let L := ((1 + (m + 3 : ℕ) * s) * exp (-δ * Real.log x₀)) *
    xiLowReciprocalNormBound a H δ
  let U := (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
    xiRosserClosedTailBound (Real.log x₀ / R) (m + 4 : ℕ) p H
  have hl : ‖∑ z ∈ xiLowHeightIndices H, iteratedBoxAverageComplex (s * x) (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x‖ / x ≤ L :=
    norm_dusartBox_low_div_le_frozen m hs hx₀ hx ha haH hδ hgap
  have hu : ‖dusartBoxXiHighSum m (s * x) x H‖ / x ≤ U :=
    norm_dusartBoxXiHighSum_div_le_frozen_closed m hs hx₀ hx hR hp hpq
      (by linarith) hpeak hreg
  have hz : ‖smoothedXiPairedSum (fun u => (dusartBoxWeight m (s * x) x u : ℂ))
      (dusartBoxSupport m (s * x) x) 0‖ / x ≤ L + U := by
    rw [smoothedXiPairedSum_box_eq_low_add_high m (mul_pos hs hxpos) hx1 H]
    exact (div_le_div_of_nonneg_right (norm_add_le _ _) hxpos.le).trans
      (by rw [add_div]; exact add_le_add hl hu)
  have hb := div_le_div_of_nonneg_right
    (abs_dusartPsiAverageError_le_zero_sum m (mul_pos hs hxpos) hx1) hxpos.le
  calc
    _ ≤ (‖smoothedXiPairedSum (fun u => (dusartBoxWeight m (s * x) x u : ℂ))
        (dusartBoxSupport m (s * x) x) 0‖ + 1 / (2 * (x ^ 2 - 1)) +
          Real.log (2 * π)) / x := hb
    _ = ‖smoothedXiPairedSum (fun u => (dusartBoxWeight m (s * x) x u : ℂ))
        (dusartBoxSupport m (s * x) x) 0‖ / x +
          (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x := by ring
    _ ≤ L + U + (1 / (2 * (x₀ ^ 2 - 1)) + Real.log (2 * π)) / x₀ :=
      add_le_add hz (dusartBox_relative_correction_le hx₀ hx)
    _ = _ := rfl

end

end PrimeFactorUnimodality
