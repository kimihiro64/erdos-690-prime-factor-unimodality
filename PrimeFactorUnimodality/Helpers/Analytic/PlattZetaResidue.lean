import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaWindow
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

set_option autoImplicit false

/-! # The zeta pole crossed by the rightward window contour

The affine zeta coordinate sends one point to `s = 1`. Its slope is `i`,
so the residue is multiplied by `-i`. The full Gamma, pi and Gaussian phase
is retained at that point; no complex residue is replaced by its real norm.
-/

open Filter
open scoped Topology

namespace PrimeFactorUnimodality

noncomputable section

/-- The window-coordinate preimage of the unique zeta pole. -/
def plattZetaPole (t₀ : ℝ) : ℂ := -(t₀ : ℂ) - Complex.I / 2

@[simp] theorem plattZetaPole_re (t₀ : ℝ) : (plattZetaPole t₀).re = -t₀ := by
  simp [plattZetaPole]

@[simp] theorem plattZetaPole_im (t₀ : ℝ) : (plattZetaPole t₀).im = -(1 / 2 : ℝ) := by
  simp [plattZetaPole]

/-- The distance to the pole is multiplied by exactly `i` in zeta coordinates. -/
theorem plattZetaArgument_sub_one (t₀ : ℝ) (z : ℂ) :
    plattZetaArgument t₀ z - 1 = Complex.I * (z - plattZetaPole t₀) := by
  apply Complex.ext <;> norm_num [plattZetaArgument, plattZetaPole,
    Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
  ring

/-- There are no other preimages of the zeta pole. -/
theorem plattZetaArgument_eq_one_iff (t₀ : ℝ) (z : ℂ) :
    plattZetaArgument t₀ z = 1 ↔ z = plattZetaPole t₀ := by
  rw [← sub_eq_zero, plattZetaArgument_sub_one, mul_eq_zero,
    or_iff_right (Complex.I_ne_zero), sub_eq_zero]

/-- The affine zeta residue, derived from Mathlib's residue-one limit. -/
theorem tendsto_plattZeta_residue (t₀ : ℝ) :
    Tendsto (fun z : ℂ => (z - plattZetaPole t₀) * riemannZeta (plattZetaArgument t₀ z))
      (𝓝[≠] (plattZetaPole t₀)) (𝓝 (-Complex.I)) := by
  have ht : Tendsto (plattZetaArgument t₀) (𝓝[≠] (plattZetaPole t₀)) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · rw [← (plattZetaArgument_eq_one_iff t₀ _).mpr rfl]
      exact (show ContinuousAt (plattZetaArgument t₀) (plattZetaPole t₀) by
        unfold plattZetaArgument
        fun_prop).continuousWithinAt.tendsto
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change plattZetaArgument t₀ z ≠ 1
      exact fun he => hz ((plattZetaArgument_eq_one_iff t₀ z).mp he)
  have hl := (riemannZeta_residue_one.comp ht).div_const Complex.I
  simp only [one_div, Complex.inv_I] at hl
  apply hl.congr'
  apply Eventually.of_forall
  intro z
  dsimp only [Function.comp_apply]
  rw [plattZetaArgument_sub_one]
  field_simp

/-- The exact complex coefficient of the pole, retaining every phase. -/
def plattZetaContourResidueValue (k : ℕ) (t₀ h x : ℝ) : ℂ :=
  -Complex.I * (plattContourIntegrand k t₀ h x (plattZetaPole t₀) *
    plattPiPhase t₀ (plattZetaPole t₀))

/-- The Gamma, exponential, phase and polynomial factors do not cancel the zeta pole. -/
theorem plattZetaContourResidueValue_ne_zero (k : ℕ) (t₀ h x : ℝ) :
    plattZetaContourResidueValue k t₀ h x ≠ 0 := by
  have hp : plattZetaPole t₀ ≠ 0 := by
    intro he
    have hr := congrArg Complex.im he
    norm_num at hr
  have hg : (1 / 4 : ℂ) + ((plattZetaPole t₀ + (t₀ : ℂ)) / 2) * Complex.I = 1 / 2 := by
    apply Complex.ext <;> norm_num [plattZetaPole, Complex.mul_re, Complex.mul_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im]
  unfold plattZetaContourResidueValue plattContourIntegrand plattPiPhase
  rw [hg]
  exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by norm_num)) (Complex.exp_ne_zero _))
        (pow_ne_zero _ (mul_ne_zero
          (mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) Complex.I_ne_zero) hp)))
      (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'))))

/-- The actual complete zeta-window integrand has the stated residue limit. -/
theorem tendsto_plattZetaContour_residue (k : ℕ) (t₀ h x : ℝ) :
    Tendsto (fun z : ℂ => (z - plattZetaPole t₀) * plattZetaContourIntegrand k t₀ h x z)
      (𝓝[≠] (plattZetaPole t₀)) (𝓝 (plattZetaContourResidueValue k t₀ h x)) := by
  have hc : Tendsto (fun z => plattContourIntegrand k t₀ h x z * plattPiPhase t₀ z)
      (𝓝[≠] (plattZetaPole t₀))
      (𝓝 (plattContourIntegrand k t₀ h x (plattZetaPole t₀) *
        plattPiPhase t₀ (plattZetaPole t₀))) :=
    ((differentiableAt_plattContourIntegrand_of_im_nonpos k t₀ h x
    (z := plattZetaPole t₀) (by simp)).continuousAt.mul
      (continuous_plattPiPhase t₀).continuousAt).continuousWithinAt.tendsto
  unfold plattZetaContourResidueValue
  convert (tendsto_plattZeta_residue t₀).mul hc using 1
  ext z
  unfold plattZetaContourIntegrand
  ring

/-- The locked simple-pole residue API agrees with the proved complete limit. -/
theorem residue_plattZetaContourIntegrand (k : ℕ) (t₀ h x : ℝ) :
    residue (plattZetaContourIntegrand k t₀ h x) (plattZetaPole t₀) =
      plattZetaContourResidueValue k t₀ h x :=
  residue_eq_of_tendsto (tendsto_plattZetaContour_residue k t₀ h x)

end

end PrimeFactorUnimodality
