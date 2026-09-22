import PrimeFactorUnimodality.Helpers.Analytic.KadiriDerivativeMass
import PrimeFactorUnimodality.Helpers.Analytic.KadiriLaplaceBounds

/-! # Sharp weighted transform remainders on arbitrary vertical lines

The actual paper weight has pole-subtracted error at most
`η² M(Re(s)/η,θ)/|s|²`. This includes negative real parts and leads to the
`M(-r/R,θ)/y²` term in Kadiri (49)--(50). The three positive-real-part
terms can instead use the previously proved cubic derivative bound.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The actual second derivative gives the exact pole-subtracted transform. -/
theorem kadiriWeight_laplace_sub_pole_eq {θ η : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) {s : ℂ} (hs : s ≠ 0) :
    finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) s -
        (kadiriWeight θ η 0 : ℂ) / s =
      finiteLaplace (fun u => (kadiriWeight₂ θ η u : ℂ)) (kadiriWeightSupport θ η) s / s ^ 2 := by
  have h := finiteLaplace_eq_pole_add
    (f := fun u => (kadiriWeight θ η u : ℂ))
    (g := fun u => (kadiriWeight₁ θ η u : ℂ))
    (h := fun u => (kadiriWeight₂ θ η u : ℂ))
    (kadiriWeightSupport_pos hθ hη).le
    (continuous_ofReal.comp_continuousOn (continuousOn_kadiriWeight θ η))
    (continuous_ofReal.comp (continuous_kadiriWeight₁ θ η)).continuousOn
    (continuous_ofReal.comp (continuous_kadiriWeight₂ θ η)).continuousOn
    (fun u hu => (hasDerivAt_kadiriWeight hu).ofReal_comp)
    (fun u _ => (hasDerivAt_kadiriWeight₁ θ η u).ofReal_comp)
    (by rw [kadiriWeight_support hθ hη, ofReal_zero])
    (by rw [kadiriWeight₁_zero hθ, ofReal_zero])
    (by rw [kadiriWeight₁_support hθ hη, ofReal_zero]) hs
  rw [h, add_sub_cancel_left]

/-- The pole-subtracted norm retains the exact weighted derivative mass. -/
theorem norm_kadiriWeight_laplace_sub_pole_le_mass {θ η : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) {s : ℂ} (hs : s ≠ 0) :
    ‖finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) s -
      (kadiriWeight θ η 0 : ℂ) / s‖ ≤
        η ^ 2 * kadiriDerivativeMass θ (s.re / η) / ‖s‖ ^ 2 := by
  rw [kadiriWeight_laplace_sub_pole_eq hθ hη hs, norm_div, norm_pow]
  exact div_le_div_of_nonneg_right (norm_kadiriWeight₂_laplace_le_mass hθ hη s) (sq_nonneg _)

/-- The real transform error has the exact same mass and quadratic denominator. -/
theorem abs_re_kadiriWeight_laplace_sub_pole_le_mass {θ η : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) {s : ℂ} (hs : s ≠ 0) :
    |(finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) s).re -
      kadiriWeight θ η 0 * s.re / (s.re ^ 2 + s.im ^ 2)| ≤
        η ^ 2 * kadiriDerivativeMass θ (s.re / η) / (s.re ^ 2 + s.im ^ 2) := by
  have h := (abs_re_le_norm _).trans (norm_kadiriWeight_laplace_sub_pole_le_mass hθ hη hs)
  simpa only [sub_re, div_re, ofReal_re, ofReal_im, zero_mul, zero_div, add_zero,
    normSq_apply, ← sq, ← normSq_eq_norm_sq] using h

/-- A lower bound on the scaled real part gives the paper's uniform vertical estimate. -/
theorem abs_re_kadiriWeight_laplace_sub_pole_le_mass_im {θ η z : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) {s : ℂ}
    (hz : z ≤ s.re / η) (hy : s.im ≠ 0) :
    |(finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) s).re -
      kadiriWeight θ η 0 * s.re / (s.re ^ 2 + s.im ^ 2)| ≤
        η ^ 2 * kadiriDerivativeMass θ z / s.im ^ 2 := by
  have hs : s ≠ 0 := by intro h; apply hy; simp [h]
  have hmass := mul_le_mul_of_nonneg_left (antitone_kadiriDerivativeMass hθ hz) (sq_nonneg η)
  refine (abs_re_kadiriWeight_laplace_sub_pole_le_mass hθ hη hs).trans
    ((div_le_div_of_nonneg_right hmass (by positivity)).trans ?_)
  exact div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg η) (kadiriDerivativeMass_nonneg hθ z))
    (sq_pos_of_ne_zero hy) (le_add_of_nonneg_left (sq_nonneg s.re))

/-- The positive-axis terms use the sharp cubic error and a uniform lower real-part bound. -/
theorem abs_re_kadiriWeight_laplace_sub_pole_le_cubic_im {θ η a : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (ha : 0 < a) {s : ℂ}
    (hs : a ≤ s.re) (hy : s.im ≠ 0) :
    |(finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) s).re -
      kadiriWeight θ η 0 * s.re / (s.re ^ 2 + s.im ^ 2)| ≤
        η ^ 3 * (-kadiriKernel₂ θ 0) / (a * s.im ^ 2) := by
  have hden : a * s.im ^ 2 ≤ s.re * (s.re ^ 2 + s.im ^ 2) :=
    (mul_le_mul_of_nonneg_right hs (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg s.re)) (ha.trans_le hs).le)
  exact (abs_re_kadiriWeight_laplace_sub_pole_le hθ hη (ha.trans_le hs)).trans
    (div_le_div_of_nonneg_left
      (mul_nonneg (pow_nonneg hη.le 3) (neg_kadiriKernel₂_zero_nonneg hθ))
      (mul_pos ha (sq_pos_of_ne_zero hy)) hden)

end

end PrimeFactorUnimodality
