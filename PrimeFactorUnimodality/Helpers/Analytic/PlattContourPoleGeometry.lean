import PrimeFactorUnimodality.Helpers.Analytic.PlattContourIntegrand

set_option autoImplicit false

/-! # Locations and regular factors of the Gamma-window contour poles

The affine Gamma argument has one preimage for every nonpositive integer.
The remaining exponential-polynomial factor is entire and nonzero at each
of these points, so no pole is canceled by the window or frequency factor.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The affine Gamma argument in the complex Fourier integrand. -/
def plattGammaArgument (t₀ : ℝ) (z : ℂ) : ℂ :=
  1 / 4 + ((z + (t₀ : ℂ)) / 2) * Complex.I

/-- The preimage of the Gamma pole at `-n`. -/
def plattGammaPole (n : ℕ) (t₀ : ℝ) : ℂ :=
  -(t₀ : ℂ) + (((2 * (n : ℝ) + 1 / 2 : ℝ)) : ℂ) * Complex.I

/-- The entire factor multiplying Gamma in the contour integrand. -/
def plattContourWeight (k : ℕ) (t₀ h u : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * (z + (t₀ : ℂ)) / 4 -
    z ^ 2 / ((2 * h ^ 2 : ℝ) : ℂ) + ((-2 * Real.pi * u : ℝ) : ℂ) * Complex.I * z) *
      (((-2 * Real.pi : ℝ) : ℂ) * Complex.I * z) ^ k

theorem plattContourIntegrand_eq_gamma_mul_weight (k : ℕ) (t₀ h u : ℝ) (z : ℂ) :
    plattContourIntegrand k t₀ h u z =
      Complex.Gamma (plattGammaArgument t₀ z) * plattContourWeight k t₀ h u z := by
  unfold plattContourIntegrand plattGammaArgument plattContourWeight
  ring

@[simp] theorem plattGammaPole_re (n : ℕ) (t₀ : ℝ) :
    (plattGammaPole n t₀).re = -t₀ := by simp [plattGammaPole]

@[simp] theorem plattGammaPole_im (n : ℕ) (t₀ : ℝ) :
    (plattGammaPole n t₀).im = 2 * (n : ℝ) + 1 / 2 := by simp [plattGammaPole]

theorem plattGammaPole_ne_zero (n : ℕ) (t₀ : ℝ) : plattGammaPole n t₀ ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  simp only [plattGammaPole_im, Complex.zero_im] at hh
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem plattGammaPole_injective (t₀ : ℝ) : Function.Injective (fun n => plattGammaPole n t₀) := by
  intro n m he
  have hh := congrArg Complex.im he
  simp only [plattGammaPole_im] at hh
  exact_mod_cast (show (n : ℝ) = m by linarith)

/-- The pole displacement is scaled by exactly `i/2`. -/
theorem plattGammaArgument_add_nat (n : ℕ) (t₀ : ℝ) (z : ℂ) :
    plattGammaArgument t₀ z + (n : ℂ) =
      (Complex.I / 2) * (z - plattGammaPole n t₀) := by
  apply Complex.ext <;>
    norm_num [plattGammaArgument, plattGammaPole, Complex.mul_re, Complex.mul_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im] <;> ring

/-- The listed points are exactly all preimages of Gamma poles. -/
theorem plattGammaArgument_eq_neg_nat_iff (n : ℕ) (t₀ : ℝ) (z : ℂ) :
    plattGammaArgument t₀ z = -(n : ℂ) ↔ z = plattGammaPole n t₀ := by
  constructor
  · intro he
    have hz : (Complex.I / 2) * (z - plattGammaPole n t₀) = 0 := by
      rw [← plattGammaArgument_add_nat, he, neg_add_cancel]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
      (div_ne_zero Complex.I_ne_zero (by norm_num)))
  · rintro rfl
    have he := plattGammaArgument_add_nat n t₀ (plattGammaPole n t₀)
    simp only [sub_self, mul_zero] at he
    exact eq_neg_of_add_eq_zero_left he

theorem analyticAt_plattContourWeight (k : ℕ) (t₀ h u : ℝ) (z : ℂ) :
    AnalyticAt ℂ (plattContourWeight k t₀ h u) z := by
  unfold plattContourWeight
  fun_prop

/-- The entire window factor cannot cancel any of the Gamma poles. -/
theorem plattContourWeight_pole_ne_zero (n k : ℕ) (t₀ h u : ℝ) :
    plattContourWeight k t₀ h u (plattGammaPole n t₀) ≠ 0 := by
  unfold plattContourWeight
  apply mul_ne_zero (Complex.exp_ne_zero _)
  apply pow_ne_zero
  exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr
    (by nlinarith [Real.pi_pos])) Complex.I_ne_zero) (plattGammaPole_ne_zero n t₀)

end

end PrimeFactorUnimodality
