import PrimeFactorUnimodality.Helpers.Analytic.PlattFourierEnvelope

set_option autoImplicit false

/-! # The actual shifted Gamma terms in the Dirichlet expansion

The phase has unit norm and the logarithmic frequency shift converts the
proved contour exponential into a real power of the Dirichlet index.
The resulting exponent includes the additional inverse square-root weight.
This bounds the terms without assuming the still-separate zeta identity.
-/

open scoped FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- The logarithmic shift of a positive Dirichlet index. -/
def plattDirichletShift (j : ℕ) : ℝ :=
  Real.log ((j : ℝ) * Real.sqrt Real.pi) / (2 * Real.pi)

/-- The inverse square-root weight and the exact complex phase. -/
def plattDirichletWeight (t₀ : ℝ) (j : ℕ) : ℂ :=
  (((j : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    (((j : ℝ) * Real.sqrt Real.pi : ℝ) : ℂ) ^ (-(t₀ : ℂ) * Complex.I)

/-- A genuine weighted, shifted Fourier transform term. -/
def plattDirichletTerm (k : ℕ) (t₀ h x : ℝ) (j : ℕ) : ℂ :=
  plattDirichletWeight t₀ j * 𝓕 (plattWindowKernel k t₀ h) (x + plattDirichletShift j)

/-- The full coefficient of the power majorant, retaining frequency dependence. -/
def plattDirichletMajorant (m k : ℕ) (t₀ h x : ℝ) : ℝ :=
  Real.exp ((2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) -
    2 * Real.pi * x * (2 * (m : ℝ) + 1 / 2)) * plattScalarCMajorant m k t₀ h *
      (Real.sqrt Real.pi) ^ (-(2 * (m : ℝ) + 1 / 2))

/-- The complex phase contributes no growth to any positive-index term. -/
theorem norm_plattDirichletWeight (t₀ : ℝ) {j : ℕ} (hj : 0 < j) :
    ‖plattDirichletWeight t₀ j‖ = (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  rw [plattDirichletWeight, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < (j : ℝ) * Real.sqrt Real.pi)]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.I_im,
    sub_self, Real.rpow_zero, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (Real.rpow_nonneg hjr.le _)

/-- The actual Dirichlet weight is the usual reciprocal square root. -/
theorem norm_plattDirichletWeight_eq_inv_sqrt (t₀ : ℝ) {j : ℕ} (hj : 0 < j) :
    ‖plattDirichletWeight t₀ j‖ = 1 / Real.sqrt j := by
  rw [norm_plattDirichletWeight t₀ hj, Real.rpow_neg (Nat.cast_nonneg j),
    ← Real.sqrt_eq_rpow, one_div]

private theorem plattDirichlet_exp_shift (m : ℕ) (h x : ℝ) {j : ℕ} (hj : 0 < j) :
    Real.exp ((2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) -
      2 * Real.pi * (x + plattDirichletShift j) * (2 * (m : ℝ) + 1 / 2)) =
    Real.exp ((2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) -
      2 * Real.pi * x * (2 * (m : ℝ) + 1 / 2)) *
      ((j : ℝ) ^ (-(2 * (m : ℝ) + 1 / 2)) *
        (Real.sqrt Real.pi) ^ (-(2 * (m : ℝ) + 1 / 2))) := by
  rw [← Real.mul_rpow (Nat.cast_nonneg j) (Real.sqrt_nonneg _),
    Real.rpow_def_of_pos (by have := hj; positivity : 0 < (j : ℝ) * Real.sqrt Real.pi),
    ← Real.exp_add]
  congr 1
  unfold plattDirichletShift
  field_simp
  ring

/-- Contour decay and the square-root coefficient give the exponent `-(2*m+1)`. -/
theorem norm_plattDirichletTerm_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) {j : ℕ} (hj : 0 < j) :
    ‖plattDirichletTerm k t₀ h x j‖ ≤
      plattDirichletMajorant m k t₀ h x * (j : ℝ) ^ (-(2 * (m : ℝ) + 1)) := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  rw [plattDirichletTerm, norm_mul, norm_plattDirichletWeight t₀ hj]
  apply (mul_le_mul_of_nonneg_left
    (norm_fourier_plattWindowKernel_le_right_shift m k hm ht₀ hh (x + plattDirichletShift j))
    (Real.rpow_nonneg hjr.le _)).trans_eq
  rw [plattDirichlet_exp_shift m h x hj]
  have hp : (j : ℝ) ^ (-(1 / 2 : ℝ)) * (j : ℝ) ^ (-(2 * (m : ℝ) + 1 / 2)) =
      (j : ℝ) ^ (-(2 * (m : ℝ) + 1)) := by
    rw [← Real.rpow_add hjr]
    congr 1
    ring
  unfold plattDirichletMajorant
  calc
    _ = (Real.exp ((2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) -
        2 * Real.pi * x * (2 * (m : ℝ) + 1 / 2)) * plattScalarCMajorant m k t₀ h *
        (Real.sqrt Real.pi) ^ (-(2 * (m : ℝ) + 1 / 2))) *
        ((j : ℝ) ^ (-(1 / 2 : ℝ)) * (j : ℝ) ^ (-(2 * (m : ℝ) + 1 / 2))) := by ring
    _ = _ := by rw [hp]

/-- The tail majorant is nonnegative throughout its analytic parameter domain. -/
theorem plattDirichletMajorant_nonneg (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) :
    0 ≤ plattDirichletMajorant m k t₀ h x := by
  unfold plattDirichletMajorant
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (plattScalarCMajorant_nonneg m k hm ht₀ hh))
    (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

end

end PrimeFactorUnimodality
