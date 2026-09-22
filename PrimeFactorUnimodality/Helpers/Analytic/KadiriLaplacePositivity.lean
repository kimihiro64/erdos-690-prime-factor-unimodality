import PrimeFactorUnimodality.Helpers.Analytic.KadiriCorrelation
import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeight
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Correlation
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Scaling

/-! # Nonnegative real Laplace transform of the actual paper weight

The exact cosine-correlation representation and its Volterra energy
identity establish the paper's condition H2 on the closed right half-plane.
Positive rescaling gives the same property for every admissible scale.
No transform-positivity hypothesis or restriction on the imaginary part
is assumed, and the boundary `Re(s)=0` is included.
The target condition is H2 in section 2.2 of
<https://www.cs.uleth.ca/~kadiri/articles/zeta-acta-04-09-07.pdf>;
the energy argument here also proves strict positivity in the open half-plane.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Set

/-- Exact transform-level form of the proved cosine correlation. -/
theorem kadiriKernel_laplace_eq_correlation {θ : ℝ}
    (hθ : Real.pi / 2 < θ ∧ θ < Real.pi) (s : ℂ) :
    finiteLaplace (fun u => (kadiriKernel θ u : ℂ)) (kadiriSupport θ) s =
      ((1 / Real.cos θ ^ 4 : ℝ) : ℂ) *
        finiteLaplace (fun u =>
          ((∫ v in (θ / Real.tan θ)..(-θ / Real.tan θ - u),
            (Real.cos (Real.tan θ * v) - Real.cos θ) *
              (Real.cos (Real.tan θ * (v + u)) - Real.cos θ) : ℝ) : ℂ))
          (kadiriSupport θ) s := by
  rw [← finiteLaplace_const_mul]
  apply finiteLaplace_congr
  intro u _
  dsimp
  rw [kadiriKernel_eq_cosineCorrelation hθ u, ofReal_mul]

/-- The unscaled paper kernel has a nonnegative real transform on the closed half-plane. -/
theorem re_kadiriKernel_laplace_nonneg {θ : ℝ}
    (hθ : Real.pi / 2 < θ ∧ θ < Real.pi) {s : ℂ} (hs : 0 ≤ s.re) :
    0 ≤ (finiteLaplace (fun u => (kadiriKernel θ u : ℂ)) (kadiriSupport θ) s).re := by
  let q : ℝ → ℝ := fun v => Real.cos (Real.tan θ * v) - Real.cos θ
  have hd : -θ / Real.tan θ - θ / Real.tan θ = kadiriSupport θ := by
    unfold kadiriSupport
    ring
  have hab : θ / Real.tan θ ≤ -θ / Real.tan θ := by
    have hp := (kadiriSupport_pos hθ).le
    rw [← hd] at hp
    linarith
  have hp := re_finiteLaplace_correlation_nonneg (q := q) (by unfold q; fun_prop) hab hs
  rw [hd] at hp
  rw [kadiriKernel_laplace_eq_correlation hθ, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity) hp

/-- The unscaled transform is strictly positive in the open right half-plane. -/
theorem re_kadiriKernel_laplace_pos {θ : ℝ}
    (hθ : Real.pi / 2 < θ ∧ θ < Real.pi) {s : ℂ} (hs : 0 < s.re) :
    0 < (finiteLaplace (fun u => (kadiriKernel θ u : ℂ)) (kadiriSupport θ) s).re := by
  let q : ℝ → ℝ := fun v => Real.cos (Real.tan θ * v) - Real.cos θ
  have hd : -θ / Real.tan θ - θ / Real.tan θ = kadiriSupport θ := by
    unfold kadiriSupport
    ring
  have hp := kadiriSupport_pos hθ
  rw [← hd, neg_div] at hp
  have hc : Real.cos θ < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hθ.1 (by linarith [Real.pi_pos])
  have hqn : ∃ c ∈ Ioo (θ / Real.tan θ) (-θ / Real.tan θ), q c ≠ 0 := by
    refine ⟨0, ⟨by linarith, by rw [neg_div]; linarith⟩, ?_⟩
    simp only [q, mul_zero, Real.cos_zero]
    linarith
  have hpos := re_finiteLaplace_correlation_pos (by unfold q; fun_prop) hqn hs
  rw [hd] at hpos
  rw [kadiriKernel_laplace_eq_correlation hθ, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  have hcoef : 0 < (1 / Real.cos θ ^ 4 : ℝ) :=
    one_div_pos.mpr (by
      have hpow := pow_pos (neg_pos.mpr hc) 4
      ring_nf at hpow
      exact hpow)
  exact mul_pos hcoef hpos

/-- The scaled, clipped paper weight has exactly the inverse-scaled kernel transform. -/
theorem kadiriWeight_laplace_eq_rescale {θ η : ℝ}
    (hθ : Real.pi / 2 < θ ∧ θ < Real.pi) (hη : 0 < η) (s : ℂ) :
    finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) s =
      finiteLaplace (fun u => (kadiriKernel θ u : ℂ)) (kadiriSupport θ) (s / (η : ℂ)) := by
  rw [← finiteLaplace_rescale _ _ _ hη.ne']
  apply finiteLaplace_congr
  intro u hu
  rw [uIcc_of_le (kadiriWeightSupport_pos hθ hη).le] at hu
  dsimp
  rw [kadiriWeight_of_mem hu, ofReal_mul]

/-- Condition H2 for the actual paper weight, including every imaginary-axis point. -/
theorem re_kadiriWeight_laplace_nonneg {θ η : ℝ}
    (hθ : Real.pi / 2 < θ ∧ θ < Real.pi) (hη : 0 < η) {s : ℂ} (hs : 0 ≤ s.re) :
    0 ≤ (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) s).re := by
  rw [kadiriWeight_laplace_eq_rescale hθ hη]
  apply re_kadiriKernel_laplace_nonneg hθ
  simpa only [div_ofReal_re] using div_nonneg hs hη.le

/-- The actual weight transform has strictly positive real part whenever `Re(s)>0`. -/
theorem re_kadiriWeight_laplace_pos {θ η : ℝ}
    (hθ : Real.pi / 2 < θ ∧ θ < Real.pi) (hη : 0 < η) {s : ℂ} (hs : 0 < s.re) :
    0 < (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) s).re := by
  rw [kadiriWeight_laplace_eq_rescale hθ hη]
  apply re_kadiriKernel_laplace_pos hθ
  simpa only [div_ofReal_re] using div_pos hs hη

end

end PrimeFactorUnimodality
