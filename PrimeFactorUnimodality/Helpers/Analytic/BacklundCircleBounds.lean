import PrimeFactorUnimodality.Helpers.Analytic.BacklundAuxiliary
import PrimeFactorUnimodality.Helpers.Analytic.ZetaRealPole
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaEulerLog
import PrimeNumberTheoremAnd.ZetaBounds

/-! # Explicit asymmetric bounds on the Backlund unit circle

Use the audited Euler continuation at truncation one, valid for every
positive real part. On the circle centred at `11/10`, the whole surrogate
is bounded by `50*T^2`, but the right semicircle is bounded by `22*T`.
Antipodal averaging will exploit this difference instead of using the
quadratic bound on the entire circle. Both signs of the height are covered.

The Euler identity and remainder bound are `Zeta0EqZeta` and `ZetaBnd_aux1b`
from the Apache-2.0 PNT dependency at
`f6147e7572ab3abe5428101bc0b13627bcb005df`. The Abel continuation restricted
to `Re(s)>1/10` is not used at the leftmost circle point `Re(s)=1/10`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Metric Set MeasureTheory

/-- A coarse, explicit zeta bound valid on the full open right half-plane. -/
theorem norm_riemannZeta_le_euler_one {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖s - 1‖ + ‖s‖ / s.re := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  let J : ℂ := ∫ x in Ioi (1 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)
  have he : riemannZeta s = (1 / 2 : ℂ) + 1 / (s - 1) + s * J := by
    rw [← Zeta0EqZeta (N := 1) (by norm_num) hs hs1]
    simp only [riemannZeta0, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.cast_zero, Nat.cast_one, zero_cpow hs0, one_cpow, div_one, div_zero,
      zero_add, add_zero]
    rw [show 1 - s = -(s - 1) by ring, div_neg, neg_div, neg_neg]
    ring
  have hj : ‖J‖ ≤ 1 / s.re := by
    have h := ZetaBnd_aux1b 1 (by norm_num) (t := s.im) hs
    simpa only [Nat.cast_one, Real.one_rpow, re_add_im] using h
  rw [he]
  calc
    _ ≤ ‖(1 / 2 : ℂ) + 1 / (s - 1)‖ + ‖s * J‖ := norm_add_le _ _
    _ ≤ (1 / 2 + 1 / ‖s - 1‖) + ‖s‖ * ‖J‖ := by
      have h := norm_add_le (1 / 2 : ℂ) (1 / (s - 1))
      norm_num only [norm_div, norm_one, norm_ofNat] at h
      simpa only [norm_mul] using add_le_add h (le_refl ‖s * J‖)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hj (norm_nonneg s)
      simpa only [mul_one_div] using add_le_add le_rfl h

/-- Elementary geometry controls both signs of a shifted unit circle. -/
theorem backlund_unit_circle_shift_bounds {z : ℂ} {t : ℝ}
    (ht : 10 ≤ |t|) (hz : z ∈ sphere (11 / 10 : ℂ) 1) :
    1 / 10 ≤ (z + t * I).re ∧ ‖z + t * I‖ ≤ 2 * |t| ∧
      1 ≤ ‖z + t * I - 1‖ ∧ ‖z + t * I - 1‖ ≤ 2 * |t| := by
  have hnorm : ‖z - (11 / 10 : ℂ)‖ = 1 := by simpa only [mem_sphere, dist_eq_norm] using hz
  have hre := abs_re_le_norm (z - (11 / 10 : ℂ))
  have him := abs_im_le_norm (z - (11 / 10 : ℂ))
  rw [hnorm] at hre him
  norm_num [sub_re, sub_im, div_ofNat_re, div_ofNat_im] at hre him
  have hzN : ‖z‖ ≤ 21 / 10 := by
    have h := norm_add_le (z - (11 / 10 : ℂ)) (11 / 10 : ℂ)
    norm_num [hnorm] at h
    exact h
  have hz1 : ‖z - 1‖ ≤ 11 / 10 := by
    have he : z - 1 = (z - (11 / 10 : ℂ)) + (1 / 10 : ℂ) := by ring
    rw [he]
    have h := norm_add_le (z - (11 / 10 : ℂ)) (1 / 10 : ℂ)
    norm_num [hnorm] at h
    exact h
  have hnormt : ‖(t : ℂ) * I‖ = |t| := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
      sub_self, add_zero]
    linarith [(abs_le.mp hre).1]
  · have h := norm_add_le z ((t : ℂ) * I)
    rw [hnormt] at h
    linarith
  · have h := abs_im_le_norm (z + t * I - 1)
    have he : |t| ≤ |z.im + t| + |z.im| := by
      simpa using abs_sub (z.im + t) z.im
    simp only [sub_im, add_im, mul_im, ofReal_re, ofReal_im, I_im, I_re,
      mul_one, mul_zero, add_zero, one_im, sub_zero] at h
    linarith
  · have he : z + t * I - 1 = (z - 1) + t * I := by ring
    rw [he]
    have h := norm_add_le (z - 1) ((t : ℂ) * I)
    rw [hnormt] at h
    linarith

/-- The full shifted circle has a quadratic surrogate bound. -/
theorem norm_backlundSurrogate_unit_circle_le {z : ℂ} {t : ℝ}
    (ht : 10 ≤ |t|) (hz : z ∈ sphere (11 / 10 : ℂ) 1) :
    ‖Backlund.zetaSurrogate (z + t * I)‖ ≤ 50 * |t| ^ 2 := by
  obtain ⟨hre, hn, hn1, hu1⟩ := backlund_unit_circle_shift_bounds ht hz
  have hs : 0 < (z + t * I).re := by linarith
  have hs1 : z + t * I ≠ 1 := by intro h; norm_num [h] at hn1
  have hζ := norm_riemannZeta_le_euler_one hs hs1
  have hi : 1 / ‖z + t * I - 1‖ ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn1
  have hq : ‖z + t * I‖ / (z + t * I).re ≤ 20 * |t| := by
    calc
      _ ≤ ‖z + t * I‖ / (1 / 10) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hre
      _ ≤ (2 * |t|) / (1 / 10) := div_le_div_of_nonneg_right hn (by norm_num)
      _ = _ := by ring
  have hb : ‖riemannZeta (z + t * I)‖ ≤ 25 * |t| := by linarith
  simp only [Backlund.zetaSurrogate, ite_eq_right hs1, norm_mul]
  calc
    _ ≤ (2 * |t|) * (25 * |t|) := mul_le_mul hu1 hb (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The right semicircle has only linear growth, using the positive Dirichlet series. -/
theorem norm_backlundSurrogate_unit_right_semicircle_le {z : ℂ} {t : ℝ}
    (ht : 10 ≤ |t|) (hz : z ∈ sphere (11 / 10 : ℂ) 1) (hr : 11 / 10 ≤ z.re) :
    ‖Backlund.zetaSurrogate (z + t * I)‖ ≤ 22 * |t| := by
  have hsre : (z + t * I).re = z.re := by simp
  have hs : 1 < (z + t * I).re := by rw [hsre]; linarith
  have hs1 : z + t * I ≠ 1 := by intro h; simp [h] at hs
  have hζ : ‖riemannZeta (z + t * I)‖ ≤ 11 := by
    have h := (norm_riemannZeta_le_norm_real hs).trans
      (norm_riemannZeta_real_le_pole_add_one hs)
    have hq : 1 / ((z + t * I).re - 1) ≤ 10 := by
      have he : (1 / 10 : ℝ) ≤ (z + t * I).re - 1 := by rw [hsre]; linarith
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 10) he
    linarith
  have hu := (backlund_unit_circle_shift_bounds ht hz).2.2.2
  simp only [Backlund.zetaSurrogate, ite_eq_right hs1, norm_mul]
  calc
    _ ≤ (2 * |t|) * 11 := mul_le_mul hu hζ (norm_nonneg _) (by positivity)
    _ = _ := by ring

end

end PrimeFactorUnimodality
