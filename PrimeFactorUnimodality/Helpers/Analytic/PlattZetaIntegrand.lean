import Mathlib.NumberTheory.LSeries.RiemannZeta
import PrimeFactorUnimodality.Helpers.Analytic.PlattDirichletTerms

set_option autoImplicit false

/-! # The zeta-window integrand and its actual Dirichlet terms

The zeta factor uses the same complex continuation as the Gamma kernel.
On the half-plane of absolute convergence it is exactly the sum of the
weighted shifted Gamma integrands. This is a pointwise identity only;
interchanging the sum and integral requires a separate domination proof.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The zeta argument corresponding to a complex window coordinate. -/
def plattZetaArgument (t₀ : ℝ) (z : ℂ) : ℂ :=
  1 / 2 + (z + (t₀ : ℂ)) * Complex.I

/-- The analytic continuation of the real-height pi phase. -/
def plattPiPhase (t₀ : ℝ) (z : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) ^ (-(z + (t₀ : ℂ)) * Complex.I)

/-- The complete Fourier integrand, including the actual zeta factor. -/
def plattZetaContourIntegrand (k : ℕ) (t₀ h x : ℝ) (z : ℂ) : ℂ :=
  plattContourIntegrand k t₀ h x z * plattPiPhase t₀ z * riemannZeta (plattZetaArgument t₀ z)

/-- The actual time-domain zeta window, with optional polynomial order. -/
def plattZetaWindow (k : ℕ) (t₀ h v : ℝ) : ℂ :=
  plattWindowKernel k t₀ h v * plattPiPhase t₀ v * riemannZeta (plattZetaArgument t₀ v)

/-- The continued positive-index term used to justify the Dirichlet interchange. -/
def plattDirichletContourTerm (k : ℕ) (t₀ h x : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  plattDirichletWeight t₀ j * plattContourIntegrand k t₀ h (x + plattDirichletShift j) z

@[simp] theorem plattZetaArgument_re (t₀ : ℝ) (z : ℂ) :
    (plattZetaArgument t₀ z).re = 1 / 2 - z.im := by
  simp [plattZetaArgument, sub_eq_add_neg]

/-- The real-line restriction is exactly the Fourier phase times the zeta window. -/
theorem plattZetaContourIntegrand_real (k : ℕ) (t₀ h x v : ℝ) :
    plattZetaContourIntegrand k t₀ h x v =
      Complex.exp (((-2 * Real.pi * v * x : ℝ) : ℂ) * Complex.I) *
        plattZetaWindow k t₀ h v := by
  rw [plattZetaContourIntegrand, plattContourIntegrand_real, plattZetaWindow]
  ring

/-- The logarithmic frequency shift combines with the weight to give the Dirichlet power. -/
theorem plattDirichletContourTerm_eq (k : ℕ) (t₀ h x : ℝ) {j : ℕ} (hj : 0 < j) (z : ℂ) :
    plattDirichletContourTerm k t₀ h x j z =
      plattContourIntegrand k t₀ h x z * plattPiPhase t₀ z *
        (1 / (j : ℂ) ^ plattZetaArgument t₀ z) := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hjc : (j : ℂ) ≠ 0 := by exact_mod_cast hj.ne'
  have hp : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hpc : (Real.sqrt Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hjpc : (((j : ℝ) * Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (mul_pos hjr hp).ne'
  unfold plattDirichletContourTerm plattDirichletWeight plattPiPhase plattZetaArgument
    plattContourIntegrand
  rw [Complex.ofReal_cpow hjr.le, Complex.ofReal_natCast]
  simp only [Complex.cpow_def_of_ne_zero hjc, Complex.cpow_def_of_ne_zero hjpc,
    Complex.cpow_def_of_ne_zero hpc]
  simp only [one_div, ← Complex.exp_neg]
  have hlog : Complex.log (((j : ℝ) * Real.sqrt Real.pi : ℝ) : ℂ) =
      Complex.log (j : ℂ) + Complex.log (Real.sqrt Real.pi : ℂ) := by
    rw [← Complex.ofReal_log (mul_pos hjr hp).le, Real.log_mul hjr.ne' hp.ne',
      Complex.ofReal_add, Complex.ofReal_log hjr.le, Complex.ofReal_log hp.le,
      Complex.ofReal_natCast]
  rw [hlog]
  have he :
      Complex.log (j : ℂ) * ((-(1 / 2 : ℝ) : ℝ) : ℂ) +
        (Complex.log (j : ℂ) + Complex.log (Real.sqrt Real.pi : ℂ)) * (-(t₀ : ℂ) * Complex.I) +
        ((Real.pi : ℂ) * (z + (t₀ : ℂ)) / 4 - z ^ 2 / ((2 * h ^ 2 : ℝ) : ℂ) +
          ((-2 * Real.pi * (x + plattDirichletShift j) : ℝ) : ℂ) * Complex.I * z) =
      ((Real.pi : ℂ) * (z + (t₀ : ℂ)) / 4 - z ^ 2 / ((2 * h ^ 2 : ℝ) : ℂ) +
          ((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I * z) +
        Complex.log (Real.sqrt Real.pi : ℂ) * (-(z + (t₀ : ℂ)) * Complex.I) -
        Complex.log (j : ℂ) * (1 / 2 + (z + (t₀ : ℂ)) * Complex.I) := by
    unfold plattDirichletShift
    rw [Real.log_mul hjr.ne' hp.ne']
    simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_ofNat, Complex.ofReal_one, Complex.ofReal_log hjr.le,
      Complex.ofReal_log hp.le, Complex.ofReal_natCast]
    field_simp
    ring
  calc
    _ = Complex.Gamma ((1 / 4 : ℂ) + ((z + (t₀ : ℂ)) / 2) * Complex.I) *
        (Complex.exp (Complex.log (j : ℂ) * ((-(1 / 2 : ℝ) : ℝ) : ℂ)) *
          Complex.exp ((Complex.log (j : ℂ) + Complex.log (Real.sqrt Real.pi : ℂ)) *
            (-(t₀ : ℂ) * Complex.I)) *
          Complex.exp ((Real.pi : ℂ) * (z + (t₀ : ℂ)) / 4 - z ^ 2 / ((2 * h ^ 2 : ℝ) : ℂ) +
            ((-2 * Real.pi * (x + plattDirichletShift j) : ℝ) : ℂ) * Complex.I * z)) *
        (((-2 * Real.pi : ℝ) : ℂ) * Complex.I * z) ^ k := by
      simp only [one_div]
      ring
    _ = _ := by
      rw [← Complex.exp_add, ← Complex.exp_add, he]
      simp only [sub_eq_add_neg, Complex.exp_add, one_div]
      ring

/-- In the absolute-convergence half-plane, the actual zeta integrand equals its term series. -/
theorem plattZetaContourIntegrand_eq_tsum (k : ℕ) (t₀ h x : ℝ) {z : ℂ}
    (hz : z.im < -(1 / 2 : ℝ)) :
    plattZetaContourIntegrand k t₀ h x z =
      ∑' n : ℕ, plattDirichletContourTerm k t₀ h x (n + 1) z := by
  unfold plattZetaContourIntegrand
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by rw [plattZetaArgument_re]; linarith),
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  simpa only [Nat.cast_add, Nat.cast_one] using
    (plattDirichletContourTerm_eq k t₀ h x (by omega : 0 < n + 1) z).symm

end

end PrimeFactorUnimodality
