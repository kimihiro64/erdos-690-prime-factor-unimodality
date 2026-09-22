import PrimeFactorUnimodality.Helpers.Analytic.KadiriLaplaceBounds
import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeightPositivity
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedStechkinFormula
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Monotonicity

/-! # Quantitative lower bound for the distinguished zero pair

This proves Kadiri (34), section 4.1.1, with symbolic parameters and the
actual compact weight: <https://www.cs.uleth.ca/~kadiri/articles/zeta-acta-04-09-07.pdf>.
Real-axis monotonicity compares three regular terms with the arguments
`1`, `δ`, and `σ₀-η₀+δ`; the cubic transform error supplies their bounds.
The singularly important transform at `σ-β` is retained exactly, including
`σ=β`. No numerical choice of the zero-free-region parameters is assumed.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real
open scoped ComplexConjugate

/-- The actual paper weight has a decreasing real-axis Laplace transform. -/
theorem antitone_re_kadiriWeight_laplace {θ η : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) :
    Antitone (fun x : ℝ =>
      (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) x).re) :=
  antitone_re_finiteLaplace (kadiriWeightSupport_pos hθ hη).le
    (continuousOn_kadiriWeight θ η) (fun u _ => kadiriWeight_nonneg hθ hη u)

/-- On the positive real axis the error has precisely a cubic denominator. -/
theorem re_kadiriWeight_laplace_real_bounds {θ η x : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hx : 0 < x) :
    kadiriWeight θ η 0 / x - η ^ 3 * (-kadiriKernel₂ θ 0) / x ^ 3 ≤
        (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) x).re ∧
      (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) x).re ≤
        kadiriWeight θ η 0 / x + η ^ 3 * (-kadiriKernel₂ θ 0) / x ^ 3 := by
  have h := abs_le.mp (abs_re_kadiriWeight_laplace_sub_pole_le hθ hη (s := (x : ℂ)) hx)
  simp only [ofReal_re, ofReal_im, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at h
  have hp : kadiriWeight θ η 0 * x / x ^ 2 = kadiriWeight θ η 0 / x := by
    field_simp
  rw [hp, show x * x ^ 2 = x ^ 3 by ring] at h
  constructor <;> linarith

/-- The exact polynomial remainder in Kadiri's distinguished-pair estimate. -/
def kadiriRetainedPairError (θ η η₀ σ₀ κ δ : ℝ) : ℝ :=
  ((κ * (1 / δ + 1 / (σ₀ - η₀ + δ)) - 1) * kadiriKernel θ 0) * η +
    ((1 + κ * (1 / δ ^ 3 + 1 / (σ₀ - η₀ + δ) ^ 3)) * (-kadiriKernel₂ θ 0)) * η ^ 3

/-- Equation (34), retaining the main transform and the exact linear/cubic error. -/
theorem kadiriWeight_retained_pair_lower_bound {θ η η₀ σ₀ σ β κ δ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)
    (hσ : σ₀ ≤ σ) (hσ₁ : σ ≤ 1) (hβ₀ : 1 - η₀ ≤ β)
    (hβσ : β ≤ σ) (hδ : 0 < δ) (hc : 0 < σ₀ - η₀ + δ) (hκ : 0 ≤ κ) :
    (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η)
        ((σ - β : ℝ) : ℂ)).re - kadiriRetainedPairError θ η η₀ σ₀ κ δ ≤
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          ((σ - β : ℝ) : ℂ) +
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          ((σ - 1 + β : ℝ) : ℂ) := by
  have hanti := antitone_re_kadiriWeight_laplace hθ hη
  have hlow := (re_kadiriWeight_laplace_real_bounds hθ hη (x := 1) zero_lt_one).1.trans
    (hanti (show σ - 1 + β ≤ 1 by linarith))
  have hδbound := (hanti (show δ ≤ σ - β + δ by linarith)).trans
    (re_kadiriWeight_laplace_real_bounds hθ hη hδ).2
  have hcbound := (hanti (show σ₀ - η₀ + δ ≤ σ - 1 + β + δ by linarith)).trans
    (re_kadiriWeight_laplace_real_bounds hθ hη hc).2
  have hupper := mul_le_mul_of_nonneg_left (add_le_add hδbound hcbound) hκ
  have hzero : kadiriWeight θ η 0 = η * kadiriKernel θ 0 := by
    rw [kadiriWeight_of_mem ⟨le_rfl, (kadiriWeightSupport_pos hθ hη).le⟩, mul_zero]
  simp only [one_pow, div_one, hzero] at hlow hupper
  simp only [smoothedLaplaceDifference, ← ofReal_add, kadiriRetainedPairError]
  simp only [div_eq_mul_inv] at hupper ⊢
  nlinarith only [hlow, hupper]

/-- The same bound at the height of an arbitrary distinguished complex zero value. -/
theorem kadiriWeight_retained_pair_at_height_lower_bound {θ η η₀ σ₀ σ κ δ : ℝ} {ρ : ℂ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)
    (hσ : σ₀ ≤ σ) (hσ₁ : σ ≤ 1) (hβ₀ : 1 - η₀ ≤ ρ.re)
    (hβσ : ρ.re ≤ σ) (hδ : 0 < δ) (hc : 0 < σ₀ - η₀ + δ) (hκ : 0 ≤ κ) :
    (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η)
        ((σ - ρ.re : ℝ) : ℂ)).re - kadiriRetainedPairError θ η η₀ σ₀ κ δ ≤
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (ρ.im : ℂ) * I) - ρ) +
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (ρ.im : ℂ) * I) - (1 - conj ρ)) := by
  have h₁ : ((σ - ρ.re : ℝ) : ℂ) = ((σ : ℂ) + (ρ.im : ℂ) * I) - ρ := by
    apply Complex.ext <;> simp
  have h₂ : ((σ - 1 + ρ.re : ℝ) : ℂ) = ((σ : ℂ) + (ρ.im : ℂ) * I) - (1 - conj ρ) := by
    apply Complex.ext <;> simp
    ring
  have h := kadiriWeight_retained_pair_lower_bound hθ hη hσ hσ₁ hβ₀ hβσ hδ hc hκ
  rw [h₁, h₂] at h
  simpa only [h₁] using h

end

end PrimeFactorUnimodality
