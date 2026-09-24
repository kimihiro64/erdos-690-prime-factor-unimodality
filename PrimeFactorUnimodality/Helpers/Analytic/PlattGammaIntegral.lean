import PrimeFactorUnimodality.Helpers.Analytic.PlattGammaMajorant
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gaussian.PolynomialMoments

set_option autoImplicit false

/-! # An integrated Gamma-window bound

The pointwise half-integer Gamma estimate is integrated using exact Gaussian
moments. The resulting finite sum supplies an independently proved bound for
the scalar `C` at every odd shift `sigma = 2*m+1`, `m >= 1`. No printed scalar
constant or precomputed zero sign is used.
-/

open MeasureTheory Finset

namespace PrimeFactorUnimodality

noncomputable section

/-- The full scalar integral, including Platt's outer frequency factor. -/
def plattScalarC (m k : ℕ) (t₀ h : ℝ) : ℝ :=
  (2 * Real.pi) ^ k * ∫ v : ℝ, plattGammaWindow m k t₀ h v

/-- The integrated polynomial majorant, expressed as a finite sum of Gamma values. -/
def plattScalarCMajorant (m k : ℕ) (t₀ h : ℝ) : ℝ :=
  (2 * Real.pi) ^ k * (Real.sqrt (2 * Real.pi) / 2 ^ m) *
    ∑ i ∈ range (m + 1), ∑ j ∈ range (k + 1),
      ((m.choose i : ℝ) * (t₀ + 2 * (m : ℝ) - 1) ^ (m - i) *
        (k.choose j : ℝ) * (2 * (m : ℝ) + 3 / 2) ^ (k - j)) *
          ((2 * h ^ 2) ^ ((((i + j : ℕ) : ℝ) + 1) / 2) *
            Real.Gamma ((((i + j : ℕ) : ℝ) + 1) / 2))

/-- The Gamma arguments remain in the open right half-plane at every real height. -/
theorem continuous_plattGammaWindow (m k : ℕ) (t₀ h : ℝ) :
    Continuous (plattGammaWindow m k t₀ h) := by
  have hg : Continuous (fun v : ℝ =>
      Complex.Gamma (((2 * (m : ℝ) + 1 : ℝ) : ℂ) / 2 +
        (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    apply (Complex.continuousAt_Gamma _ ?_).comp
      (show ContinuousAt (fun v : ℝ =>
        (((2 * (m : ℝ) + 1 : ℝ) : ℂ) / 2 +
          (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I)) v by fun_prop)
    intro n hn
    have hr := congrArg Complex.re hn
    norm_num at hr
    linarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n]
  exact (hg.norm.mul (by fun_prop)).mul (by fun_prop)

private def windowMajorant (m k : ℕ) (t₀ h v : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) / 2 ^ m *
    ((t₀ + 2 * (m : ℝ) - 1 + |v|) ^ m *
      (2 * (m : ℝ) + 3 / 2 + |v|) ^ k * Real.exp (-(1 / (2 * h ^ 2)) * v ^ 2))

private theorem integrable_windowMajorant (m k : ℕ) (t₀ : ℝ) {h : ℝ} (hh : 0 < h) :
    Integrable (windowMajorant m k t₀ h) := by
  exact (Real.integrable_add_abs_pow_mul_add_abs_pow_mul_exp_neg_mul_sq m k
    (t₀ + 2 * (m : ℝ) - 1) (2 * (m : ℝ) + 3 / 2)
    (by positivity : 0 < 1 / (2 * h ^ 2))).const_mul _

private theorem plattGammaWindow_le_windowMajorant (m k : ℕ) (hm : 1 ≤ m)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (h v : ℝ) :
    plattGammaWindow m k t₀ h v ≤ windowMajorant m k t₀ h v := by
  have he : -(1 / (2 * h ^ 2)) * v ^ 2 = -v ^ 2 / (2 * h ^ 2) := by ring
  have hs : t₀ + 2 * (m : ℝ) - 1 + |v| = t₀ + |v| + 2 * (m : ℝ) - 1 := by ring
  simpa only [windowMajorant, he, hs, mul_assoc] using
    plattGammaWindow_le_polynomial m k hm ht₀ h v

/-- The true Gamma window is integrable, not merely assigned an undefined integral. -/
theorem integrable_plattGammaWindow (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) :
    Integrable (plattGammaWindow m k t₀ h) := by
  apply (integrable_windowMajorant m k t₀ hh).mono'
    (continuous_plattGammaWindow m k t₀ h).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro v
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ plattGammaWindow m k t₀ h v by
    unfold plattGammaWindow
    positivity)]
  exact plattGammaWindow_le_windowMajorant m k hm ht₀ h v

/-- A finite Gamma sum bounds the full scalar error constant at every admissible odd shift. -/
theorem plattScalarC_le_majorant (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) :
    plattScalarC m k t₀ h ≤ plattScalarCMajorant m k t₀ h := by
  have hi := integral_mono (integrable_plattGammaWindow m k hm ht₀ hh)
    (integrable_windowMajorant m k t₀ hh)
    (plattGammaWindow_le_windowMajorant m k hm ht₀ h)
  unfold windowMajorant at hi
  rw [integral_const_mul,
    Real.integral_add_abs_pow_mul_add_abs_pow_mul_exp_neg_mul_sq m k
      (t₀ + 2 * (m : ℝ) - 1) (2 * (m : ℝ) + 3 / 2)
      (by positivity : 0 < 1 / (2 * h ^ 2))] at hi
  simp only [one_div_one_div] at hi
  exact (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (2 * Real.pi) ^ k)).trans_eq
    (by unfold plattScalarCMajorant; ring)

end

end PrimeFactorUnimodality
