import PrimeFactorUnimodality.Helpers.Analytic.GammaStirlingExpansion
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.ExponentialStability
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.ShiftedBound

/-! # Explicit arbitrary-order enclosures of complex Gamma

The normalized logarithmic approximation has a rational coefficient budget
times an inverse power of the imaginary height. Exponentiation then encloses
the actual Gamma function, including amplitude and phase. This module states
the arithmetic error inputs explicitly; it does not assert computed values.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Polynomial Set

/-- The finite, completely normalized complex logarithmic approximation. -/
def gammaStirlingApprox (M : ℕ) (z : ℂ) : ℂ :=
  ((z - 1 / 2) * log z - z) + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) +
    gammaStirlingCorrection M z

/-- An explicit height-decaying error with a computable rational Bernoulli budget. -/
def gammaStirlingError (M : ℕ) (H : ℝ) : ℝ :=
  (M.factorial : ℝ) * (bernoulliCoeffBudget (M + 1) : ℝ) *
    ((1 + 1 / (M : ℝ)) * H ^ (-(M : ℝ)))

/-- The remainder budget uses only rational operations and natural powers at rational radii. -/
theorem gammaStirlingError_eq_div_pow (M : ℕ) {H : ℝ} (hH : 0 < H) :
    gammaStirlingError M H = (M.factorial : ℝ) * (bernoulliCoeffBudget (M + 1) : ℝ) *
      (1 + 1 / (M : ℝ)) / H ^ M := by
  rw [gammaStirlingError, Real.rpow_neg hH.le, Real.rpow_natCast]
  ring

/-- Every positive lower radius on the horizontal ray gives a complete logarithmic enclosure. -/
theorem norm_gammaRightLog_sub_stirlingApprox_le_radius {z : ℂ} (hz : 0 < z.re)
    {M : ℕ} (hM : 1 ≤ M) {H : ℝ} (hH : 0 < H)
    (hB : ∀ x : ℝ, 0 ≤ x → H ≤ ‖z + (x : ℂ)‖) :
    ‖gammaRightLog z - gammaStirlingApprox M z‖ ≤ gammaStirlingError M H := by
  have he : gammaRightLog z - gammaStirlingApprox M z =
      -(M.factorial : ℂ) * ∫ x : ℝ in Ioi 0,
        (bernoulliPeriodic (M + 1) x : ℂ) * (z + (x : ℂ))⁻¹ ^ (M + 1) := by
    rw [gammaRightLog_eq_stirling_expansion hz hM]
    unfold gammaStirlingApprox
    ring
  have hb := norm_bernoulliPeriodic_inv_pow_tail_le_of_lower_bound (M + 1) (p := M + 1)
    (by omega) hz hH hB
  rw [bernoulliCoeffBound_eq_budget] at hb
  have h1 : ((M + 1 : ℕ) : ℝ) - 1 = M := by push_cast; ring
  have h2 : 1 - ((M + 1 : ℕ) : ℝ) = -(M : ℝ) := by push_cast; ring
  rw [h1, h2] at hb
  rw [he, norm_mul, norm_neg, norm_natCast]
  exact (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg M.factorial)).trans_eq (by
    unfold gammaStirlingError
    ring)

/-- Imaginary height gives an explicit enclosure at every positive truncation order. -/
theorem norm_gammaRightLog_sub_stirlingApprox_le {z : ℂ} (hz : 0 < z.re)
    {M : ℕ} (hM : 1 ≤ M) (him : 0 < |z.im|) :
    ‖gammaRightLog z - gammaStirlingApprox M z‖ ≤ gammaStirlingError M |z.im| :=
  norm_gammaRightLog_sub_stirlingApprox_le_radius hz hM him
    (fun x _ => by simpa using abs_im_le_norm (z + (x : ℂ)))

/-- The real part gives an enclosure even on the positive real axis. -/
theorem norm_gammaRightLog_sub_stirlingApprox_le_re {z : ℂ} (hz : 0 < z.re)
    {M : ℕ} (hM : 1 ≤ M) :
    ‖gammaRightLog z - gammaStirlingApprox M z‖ ≤ gammaStirlingError M z.re := by
  apply norm_gammaRightLog_sub_stirlingApprox_le_radius hz hM hz
  intro x hx
  have h := re_le_norm (z + (x : ℂ))
  simp only [add_re, ofReal_re] at h
  linarith

/-- Transport a full complex logarithmic enclosure through exponentiation to actual Gamma. -/
theorem norm_Gamma_sub_exp_le_of_log_enclosure {z w : ℂ} (hz : 0 < z.re) {ε : ℝ}
    (hε : ‖gammaRightLog z - w‖ ≤ ε) :
    ‖Gamma z - exp w‖ ≤ Real.exp w.re * (Real.exp ε - 1) := by
  rw [← exp_gammaRightLog hz]
  exact norm_exp_sub_exp_le_of_norm_sub_le hε

/-- A closed arbitrary-order enclosure of Gamma itself, not just its argument. -/
theorem norm_Gamma_sub_stirling_exp_le {z : ℂ} (hz : 0 < z.re)
    {M : ℕ} (hM : 1 ≤ M) (him : 0 < |z.im|) :
    ‖Gamma z - exp (gammaStirlingApprox M z)‖ ≤
      Real.exp (gammaStirlingApprox M z).re * (Real.exp (gammaStirlingError M |z.im|) - 1) :=
  norm_Gamma_sub_exp_le_of_log_enclosure hz (norm_gammaRightLog_sub_stirlingApprox_le hz hM him)

/-- A full Gamma enclosure valid throughout the open right half-plane, including zero height. -/
theorem norm_Gamma_sub_stirling_exp_le_re {z : ℂ} (hz : 0 < z.re)
    {M : ℕ} (hM : 1 ≤ M) :
    ‖Gamma z - exp (gammaStirlingApprox M z)‖ ≤
      Real.exp (gammaStirlingApprox M z).re * (Real.exp (gammaStirlingError M z.re) - 1) :=
  norm_Gamma_sub_exp_le_of_log_enclosure hz (norm_gammaRightLog_sub_stirlingApprox_le_re hz hM)

/-- Rounded logarithmic arithmetic and rounded exponentiation retain both error budgets. -/
theorem norm_Gamma_sub_rounded_stirling_le {z q w : ℂ} (hz : 0 < z.re)
    {M : ℕ} (hM : 1 ≤ M) (him : 0 < |z.im|) {δ η : ℝ}
    (hq : ‖gammaStirlingApprox M z - q‖ ≤ δ) (hw : ‖exp q - w‖ ≤ η) :
    ‖Gamma z - w‖ ≤
      Real.exp q.re * (Real.exp (gammaStirlingError M |z.im| + δ) - 1) + η := by
  have hlog : ‖gammaRightLog z - q‖ ≤ gammaStirlingError M |z.im| + δ :=
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      (add_le_add (norm_gammaRightLog_sub_stirlingApprox_le hz hM him) hq)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (norm_Gamma_sub_exp_le_of_log_enclosure hz hlog) hw)

end

end PrimeFactorUnimodality
