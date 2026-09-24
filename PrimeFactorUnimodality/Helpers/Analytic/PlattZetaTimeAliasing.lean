import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaWindow
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.PolynomialGaussianAliasing

set_option autoImplicit false

/-! # The actual zeta window's time-side alias budget

The elementary critical-line zeta bound adds one polynomial degree to the
Gamma window. Both degrees are kept, with separate exact geometric sums.
The width condition is imposed on the larger degree and makes every
denominator positive, for every natural order and signed center.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The two degrees introduced by the critical-line zeta growth estimate. -/
def plattZetaTimeDegree (k : ℕ) : Bool → ℕ
  | false => k
  | true => k + 1

/-- The Gamma bound times respectively the constant and linear zeta terms. -/
def plattZetaTimeCoeff (k : ℕ) (t₀ : ℝ) : Bool → ℝ
  | false => 5 * (2 * Real.pi) ^ k * (4 + 2 * |t₀|)
  | true => 10 * (2 * Real.pi) ^ k

theorem plattZetaTimeCoeff_nonneg (k : ℕ) (t₀ : ℝ) (i : Bool) :
    0 ≤ plattZetaTimeCoeff k t₀ i := by
  cases i <;> simp only [plattZetaTimeCoeff] <;> positivity

/-- A concrete two-degree Gaussian envelope for the actual window. -/
theorem norm_plattZetaWindow_le_polynomialGaussian (k : ℕ) (t₀ h v : ℝ) :
    ‖plattZetaWindow k t₀ h v‖ ≤
      ∑ i : Bool, plattZetaTimeCoeff k t₀ i * |v| ^ plattZetaTimeDegree k i *
        Real.exp (-(1 / (2 * h ^ 2)) * v ^ 2) := by
  rw [plattZetaWindow, norm_mul, norm_mul, norm_plattPiPhase]
  simp only [Complex.ofReal_im, Real.rpow_zero, mul_one]
  apply (mul_le_mul (norm_plattWindowKernel_le_five k t₀ h v)
    (norm_riemannZeta_plattArgument_real_le t₀ v) (norm_nonneg _) (by positivity)).trans_eq
  rw [show -v ^ 2 / (2 * h ^ 2) = -(1 / (2 * h ^ 2)) * v ^ 2 by ring]
  simp only [Fintype.sum_bool, plattZetaTimeCoeff, plattZetaTimeDegree, pow_succ,
    mul_pow]
  ring

/-- The larger degree's width condition gives positive decay for both terms. -/
theorem plattZetaTimeAlias_decay (k : ℕ) {h B : ℝ} (hh : 0 < h)
    (hk : 4 * ((k : ℝ) + 1) * h ^ 2 < B ^ 2) (i : Bool) :
    2 * (plattZetaTimeDegree k i : ℝ) < (1 / (2 * h ^ 2)) * B ^ 2 := by
  have hd : 2 * ((k : ℝ) + 1) < B ^ 2 / (2 * h ^ 2) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * h ^ 2)).mpr
    nlinarith
  rw [show (1 / (2 * h ^ 2)) * B ^ 2 = B ^ 2 / (2 * h ^ 2) by ring]
  cases i <;> simp only [plattZetaTimeDegree, Nat.cast_add, Nat.cast_one] <;> linarith

/-- The actual zeta time periodization. -/
def plattZetaTimePeriodization (k : ℕ) (t₀ h B v : ℝ) : ℂ :=
  ∑' n : ℤ, plattZetaWindow k t₀ h (v + (n : ℝ) * B)

/-- A finite closed expression for both complete time-alias tails. -/
def plattZetaTimeAliasBound (k : ℕ) (t₀ h B : ℝ) : ℝ :=
  ∑ i : Bool, 2 * plattZetaTimeCoeff k t₀ i * (B / 2) ^ plattZetaTimeDegree k i *
    Real.exp (-B ^ 2 / (8 * h ^ 2)) /
      (1 - Real.exp (2 * (plattZetaTimeDegree k i : ℝ) - B ^ 2 / (2 * h ^ 2)))

theorem plattZetaTimeAlias_denominator_pos (k : ℕ) {h B : ℝ} (hh : 0 < h)
    (hk : 4 * ((k : ℝ) + 1) * h ^ 2 < B ^ 2) (i : Bool) :
    0 < 1 - Real.exp (2 * (plattZetaTimeDegree k i : ℝ) - B ^ 2 / (2 * h ^ 2)) := by
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have hd := plattZetaTimeAlias_decay k hh hk i
  rw [show (1 / (2 * h ^ 2)) * B ^ 2 = B ^ 2 / (2 * h ^ 2) by ring] at hd
  linarith

/-- All actual time translates converge, retaining the extra zeta growth degree. -/
theorem summable_plattZetaTimePeriodization (k : ℕ) (t₀ : ℝ) {h B v : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hk : 4 * ((k : ℝ) + 1) * h ^ 2 < B ^ 2)
    (hv : |v| ≤ B / 2) :
    Summable (fun n : ℤ => plattZetaWindow k t₀ h (v + (n : ℝ) * B)) :=
  Fourier.summable_lattice_of_finite_polynomialGaussian_bound
    (s := Finset.univ) (fun i _ => plattZetaTimeCoeff_nonneg k t₀ i) (by positivity)
    hB (fun i _ => plattZetaTimeAlias_decay k hh hk i) hv
    (norm_plattZetaWindow_le_polynomialGaussian k t₀ h)

/-- The actual time-alias error is bounded by the explicit two-degree expression. -/
theorem norm_plattZetaTimePeriodization_sub_le (k : ℕ) (t₀ : ℝ) {h B v : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hk : 4 * ((k : ℝ) + 1) * h ^ 2 < B ^ 2)
    (hv : |v| ≤ B / 2) :
    ‖plattZetaTimePeriodization k t₀ h B v - plattZetaWindow k t₀ h v‖ ≤
      plattZetaTimeAliasBound k t₀ h B := by
  have ht := Fourier.norm_periodization_sub_le_of_finite_polynomialGaussian_bound
    (s := Finset.univ) (fun i _ => plattZetaTimeCoeff_nonneg k t₀ i) (by positivity)
    hB (fun i _ => plattZetaTimeAlias_decay k hh hk i) hv
    (norm_plattZetaWindow_le_polynomialGaussian k t₀ h)
  have he : -(1 / (2 * h ^ 2)) * (B / 2) ^ 2 = -B ^ 2 / (8 * h ^ 2) := by ring
  have hd : (1 / (2 * h ^ 2)) * B ^ 2 = B ^ 2 / (2 * h ^ 2) := by ring
  simpa only [plattZetaTimePeriodization, plattZetaTimeAliasBound, he, hd] using ht

end

end PrimeFactorUnimodality
