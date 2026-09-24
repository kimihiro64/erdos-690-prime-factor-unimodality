import PrimeFactorUnimodality.Helpers.Analytic.GammaStirlingBounds
import PrimeFactorUnimodality.Helpers.Analytic.PlattWindowKernel

/-! # Compensated Stirling evaluation of the actual Platt kernel

Combine the Gamma logarithm and the real exponential compensation before
exponentiating. This avoids separately representing exponentially tiny Gamma
values and exponentially large compensation factors at high ordinates.
One base-value enclosure is reused for every polynomial kernel order.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The quarter-line argument used by the actual Gamma-window kernel. -/
def plattKernelArgument (t₀ v : ℝ) : ℂ :=
  (1 / 4 : ℂ) + (((v + t₀) / 2 : ℝ) : ℂ) * I

/-- The compensation and Gaussian window, kept in logarithmic form. -/
def plattKernelLogShift (t₀ h v : ℝ) : ℝ :=
  Real.pi * (v + t₀) / 4 - v ^ 2 / (2 * h ^ 2)

/-- The larger of the real-part and imaginary-height radii, positive even at zero height. -/
def plattGammaRadius (t₀ v : ℝ) : ℝ := max (1 / 4) |(v + t₀) / 2|

/-- The normalized finite approximation with compensation already combined. -/
def plattCompensatedLogApprox (M : ℕ) (t₀ h v : ℝ) : ℂ :=
  gammaStirlingApprox M (plattKernelArgument t₀ v) + (plattKernelLogShift t₀ h v : ℂ)

/-- The polynomial factor shared by every occurrence of a fixed kernel order. -/
def plattKernelPower (k : ℕ) (v : ℝ) : ℂ := (((-2 * Real.pi * v : ℝ) : ℂ) * I) ^ k

/-- Every point of the horizontal Gamma ray has the stated positive lower radius. -/
theorem plattGammaRadius_le_norm_add (t₀ v x : ℝ) (hx : 0 ≤ x) :
    plattGammaRadius t₀ v ≤ ‖plattKernelArgument t₀ v + (x : ℂ)‖ := by
  apply max_le
  · have h := re_le_norm (plattKernelArgument t₀ v + (x : ℂ))
    have hr : (plattKernelArgument t₀ v).re = 1 / 4 := by norm_num [plattKernelArgument]
    simp only [add_re, ofReal_re, hr] at h
    linarith
  · simpa [plattKernelArgument] using abs_im_le_norm (plattKernelArgument t₀ v + (x : ℂ))

/-- The true kernel is exactly one compensated exponential and one polynomial factor. -/
theorem plattWindowKernel_eq_compensated_exp (k : ℕ) (t₀ h v : ℝ) :
    plattWindowKernel k t₀ h v =
      exp (gammaRightLog (plattKernelArgument t₀ v) + (plattKernelLogShift t₀ h v : ℂ)) *
        plattKernelPower k v := by
  rw [exp_add, exp_gammaRightLog (by norm_num [plattKernelArgument]), ← ofReal_exp]
  rfl

/-- The exact polynomial factor has an explicit norm at every natural order. -/
theorem norm_plattKernelPower (k : ℕ) (v : ℝ) :
    ‖plattKernelPower k v‖ = (2 * Real.pi * |v|) ^ k := by
  simp [plattKernelPower, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- The input error includes the analytic tail and both rounds of numerical approximation. -/
def plattStirlingInputError (M : ℕ) (t₀ v : ℝ) (q : ℂ) (δ η : ℝ) : ℝ :=
  Real.exp q.re * (Real.exp (gammaStirlingError M (plattGammaRadius t₀ v) + δ) - 1) + η

/-- Enclosed compensated logarithm and exponential give an actual base-kernel enclosure. -/
theorem norm_plattWindowKernel_zero_sub_stirling_le {M : ℕ} (hM : 1 ≤ M)
    (t₀ h v : ℝ) {q b : ℂ} {δ η : ℝ}
    (hq : ‖plattCompensatedLogApprox M t₀ h v - q‖ ≤ δ) (hb : ‖exp q - b‖ ≤ η) :
    ‖plattWindowKernel 0 t₀ h v - b‖ ≤ plattStirlingInputError M t₀ v q δ η := by
  have hz : 0 < (plattKernelArgument t₀ v).re := by norm_num [plattKernelArgument]
  have hH : 0 < plattGammaRadius t₀ v := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hg := norm_gammaRightLog_sub_stirlingApprox_le_radius hz hM hH
    (plattGammaRadius_le_norm_add t₀ v)
  have he : ‖gammaRightLog (plattKernelArgument t₀ v) + (plattKernelLogShift t₀ h v : ℂ) -
      plattCompensatedLogApprox M t₀ h v‖ ≤ gammaStirlingError M (plattGammaRadius t₀ v) := by
    simpa only [plattCompensatedLogApprox, add_sub_add_right_eq_sub] using hg
  have hl := (norm_sub_le_norm_sub_add_norm_sub _ _ q).trans (add_le_add he hq)
  rw [plattWindowKernel_eq_compensated_exp]
  simp only [plattKernelPower, pow_zero, mul_one]
  exact (norm_sub_le_norm_sub_add_norm_sub _ (exp q) b).trans
    (add_le_add (norm_exp_sub_exp_le_of_norm_sub_le hl) hb)

/-- Every natural kernel order reuses the same enclosed base value and a rounded power. -/
theorem norm_plattWindowKernel_sub_rounded_power_le (k : ℕ) (t₀ h v : ℝ)
    {b p w : ℂ} {ε ν ρ : ℝ}
    (hb : ‖plattWindowKernel 0 t₀ h v - b‖ ≤ ε)
    (hp : ‖plattKernelPower k v - p‖ ≤ ν) (hw : ‖b * p - w‖ ≤ ρ) :
    ‖plattWindowKernel k t₀ h v - w‖ ≤
      ε * (2 * Real.pi * |v|) ^ k + ‖b‖ * ν + ρ := by
  have he : plattWindowKernel k t₀ h v - b * p =
      (plattWindowKernel 0 t₀ h v - b) * plattKernelPower k v +
        b * (plattKernelPower k v - p) := by
    simp only [plattWindowKernel, pow_zero, mul_one, plattKernelPower]
    ring
  have hb' : ‖plattWindowKernel k t₀ h v - b * p‖ ≤
      ε * (2 * Real.pi * |v|) ^ k + ‖b‖ * ν := by
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_plattKernelPower]
    exact add_le_add (mul_le_mul_of_nonneg_right hb (by positivity))
      (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
  exact (norm_sub_le_norm_sub_add_norm_sub _ (b * p) w).trans (add_le_add hb' hw)

end

end PrimeFactorUnimodality
