import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeightEndpoints

/-! # Separating the kernel into elementary exponential-integral terms

Expand the two shifted sines in the actual smoothing kernel. The result
uses an affine term, a constant cosine, a linearly weighted cosine, and
one sine term, all at the same frequency. This is an exact identity on
the entire real line, before multiplying by the exponential weight.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The sine coefficient after expanding the shifted phases. -/
def kadiriKernelSineCoefficient (θ : ℝ) : ℝ :=
  2 * cos θ / sin θ - cos (2 * θ) / sin (2 * θ)

/-- The actual frequency is nonzero throughout the paper's parameter domain. -/
theorem kadiriKernel_frequency_ne_zero {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) :
    tan θ ≠ 0 := by
  have hs := sin_pos_of_pos_of_lt_pi (pi_div_two_pos.trans hθ.1) hθ.2
  have hc := cos_neg_of_pi_div_two_lt_of_lt hθ.1 (by linarith [pi_pos])
  rw [tan_eq_sin_div_cos]
  exact (div_neg_of_pos_of_neg hs hc).ne

/-- Shifted trigonometric phases reduce to a common-frequency affine combination. -/
theorem kadiriKernel_eq_normalForm {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (u : ℝ) :
    kadiriKernel θ u = (1 + tan θ ^ 2) *
      ((1 + tan θ ^ 2) / 2 * ((kadiriSupport θ - u) * cos (tan θ * u)) +
        (kadiriSupport θ - u) + 2 + cos (tan θ * u) +
          kadiriKernelSineCoefficient θ * sin (tan θ * u)) := by
  have hs : sin θ ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (pi_div_two_pos.trans hθ.1) hθ.2).ne'
  have hc : cos θ ≠ 0 :=
    (cos_neg_of_pi_div_two_lt_of_lt hθ.1 (by linarith [pi_pos])).ne
  have hs2 : sin (2 * θ) ≠ 0 := by
    rw [sin_two_mul]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hs) hc
  unfold kadiriKernel kadiriKernelSineCoefficient
  rw [sin_add, sin_add, mul_comm u (tan θ)]
  field_simp
  ring

end

end PrimeFactorUnimodality
