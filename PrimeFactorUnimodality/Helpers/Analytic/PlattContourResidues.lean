import PrimeFactorUnimodality.Helpers.Analytic.PlattContourPoleGeometry
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.Residue
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

set_option autoImplicit false

/-! # Exact simple-pole residues of the actual contour integrand

Gamma recurrence and affine transport give the inverse-slope factor `-2i`.
The entire window factor is evaluated at each pole. These are residue limits
of the actual Fourier integrand, not externally supplied residue data.
The residue definition is the simple-pole limit from the locked PNT dependency.
-/

open Filter
open scoped Topology

namespace PrimeFactorUnimodality

noncomputable section

/-- The exact coefficient of the simple pole, including the window and Fourier phase. -/
def plattContourResidueValue (n k : ℕ) (t₀ h u : ℝ) : ℂ :=
  (-2 * Complex.I) * ((-1 : ℂ) ^ n / (n.factorial : ℂ)) *
    plattContourWeight k t₀ h u (plattGammaPole n t₀)

theorem plattContourResidueValue_ne_zero (n k : ℕ) (t₀ h u : ℝ) :
    plattContourResidueValue n k t₀ h u ≠ 0 := by
  unfold plattContourResidueValue
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    (div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero n)))
      (plattContourWeight_pole_ne_zero n k t₀ h u)

/-- The shifted Gamma factor has the transported residue `(-2i)*(-1)^n/n!`. -/
theorem tendsto_plattGamma_residue (n : ℕ) (t₀ : ℝ) :
    Tendsto (fun z : ℂ => (z - plattGammaPole n t₀) *
      Complex.Gamma (plattGammaArgument t₀ z)) (𝓝[≠] (plattGammaPole n t₀))
      (𝓝 ((-2 * Complex.I) * ((-1 : ℂ) ^ n / (n.factorial : ℂ)))) := by
  have harg (z : ℂ) : (Complex.I / 2) * z +
      (1 / 4 + ((t₀ : ℂ) / 2) * Complex.I) = plattGammaArgument t₀ z := by
    unfold plattGammaArgument
    ring
  have hp : (Complex.I / 2) * plattGammaPole n t₀ +
      (1 / 4 + ((t₀ : ℂ) / 2) * Complex.I) = -(n : ℂ) := by
    rw [harg]
    exact (plattGammaArgument_eq_neg_nat_iff n t₀ _).mpr rfl
  have ht := Complex.tendsto_sub_mul_Gamma_affine n
    (div_ne_zero Complex.I_ne_zero (by norm_num)) hp
  have hc : ((-1 : ℂ) ^ n / (n.factorial : ℂ)) / (Complex.I / 2) =
      (-2 * Complex.I) * ((-1 : ℂ) ^ n / (n.factorial : ℂ)) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, Complex.inv_I]
    ring
  simpa only [harg, hc] using ht

/-- Multiplication by the analytic window transports the complete residue limit. -/
theorem tendsto_plattContour_residue (n k : ℕ) (t₀ h u : ℝ) :
    Tendsto (fun z : ℂ => (z - plattGammaPole n t₀) * plattContourIntegrand k t₀ h u z)
      (𝓝[≠] (plattGammaPole n t₀)) (𝓝 (plattContourResidueValue n k t₀ h u)) := by
  have hw : Tendsto (plattContourWeight k t₀ h u) (𝓝[≠] (plattGammaPole n t₀))
      (𝓝 (plattContourWeight k t₀ h u (plattGammaPole n t₀))) :=
    (analyticAt_plattContourWeight k t₀ h u
      (plattGammaPole n t₀)).continuousAt.continuousWithinAt.tendsto
  unfold plattContourResidueValue
  convert (tendsto_plattGamma_residue n t₀).mul hw using 1
  ext z
  rw [plattContourIntegrand_eq_gamma_mul_weight]
  ring

/-- The dependency's simple-pole residue equals the exact value just proved. -/
theorem residue_plattContourIntegrand (n k : ℕ) (t₀ h u : ℝ) :
    residue (plattContourIntegrand k t₀ h u) (plattGammaPole n t₀) =
      plattContourResidueValue n k t₀ h u :=
  residue_eq_of_tendsto (tendsto_plattContour_residue n k t₀ h u)

end

end PrimeFactorUnimodality
