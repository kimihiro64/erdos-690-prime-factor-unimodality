import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeightEndpoints
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.CosineCorrelation

/-! # Cosine-correlation representation of the actual smoothing kernel

The kernel equals the overlap integral of two translated cosine bumps.
The representation is obtained by exact integration, and proves its
nonnegativity throughout its support for every admissible angle.
The kernel being evaluated is the formula in section 2 of
<https://arxiv.org/abs/1410.3926>.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real Set

variable {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π)

include hθ

private theorem sin_pos : 0 < sin θ :=
  sin_pos_of_pos_of_lt_pi (pi_div_two_pos.trans hθ.1) hθ.2

private theorem cos_neg : cos θ < 0 :=
  cos_neg_of_pi_div_two_lt_of_lt hθ.1 (by linarith [pi_pos])

private theorem tan_neg : tan θ < 0 := by
  rw [tan_eq_sin_div_cos]
  exact div_neg_of_pos_of_neg (sin_pos hθ) (cos_neg hθ)

/-- Exact overlap representation; on the support its integrand is nonnegative. -/
theorem kadiriKernel_eq_cosineCorrelation (u : ℝ) :
    kadiriKernel θ u = (1 / cos θ ^ 4) *
      ∫ v in (θ / tan θ)..(-θ / tan θ - u),
        (cos (tan θ * v) - cos θ) * (cos (tan θ * (v + u)) - cos θ) := by
  have ht := (tan_neg hθ).ne
  have hs := (sin_pos hθ).ne'
  have hc := (cos_neg hθ).ne
  have hsec : 1 + tan θ ^ 2 = 1 / cos θ ^ 2 := by
    rw [tan_eq_sin_div_cos]
    field_simp
    nlinarith [sin_sq_add_cos_sq θ]
  rw [intervalIntegral.integral_cos_sub_mul_cos_sub ht]
  have h₁ : 2 * tan θ * (-θ / tan θ - u) + tan θ * u = -(2 * θ + u * tan θ) := by
    field_simp
    ring
  have h₂ : tan θ * (-θ / tan θ - u) = -(θ + u * tan θ) := by
    field_simp
    ring
  have h₃ : tan θ * (-θ / tan θ - u + u) = -θ := by
    field_simp
    ring
  have h₄ : 2 * tan θ * (θ / tan θ) + tan θ * u = 2 * θ + u * tan θ := by
    field_simp
  have h₅ : tan θ * (θ / tan θ) = θ := mul_div_cancel₀ _ ht
  have h₆ : tan θ * (θ / tan θ + u) = θ + u * tan θ := by
    field_simp
  rw [h₁, h₂, h₃, h₄, h₅, h₆]
  simp only [Real.sin_neg]
  rw [kadiriKernel, hsec, kadiriSupport, mul_comm (tan θ) u,
    tan_eq_sin_div_cos, sin_two_mul]
  field_simp
  ring

/-- Each cosine bump is nonnegative inside its symmetric support. -/
theorem kadiri_cosineBump_nonneg {v : ℝ}
    (hv : v ∈ Icc (θ / tan θ) (-θ / tan θ)) :
    0 ≤ cos (tan θ * v) - cos θ := by
  have ht := tan_neg hθ
  have hlo := mul_le_mul_of_nonpos_left hv.2 ht.le
  have hhi := mul_le_mul_of_nonpos_left hv.1 ht.le
  have h₁ : tan θ * (-θ / tan θ) = -θ := mul_div_cancel₀ _ ht.ne
  have h₂ : tan θ * (θ / tan θ) = θ := mul_div_cancel₀ _ ht.ne
  rw [h₁] at hlo
  rw [h₂] at hhi
  have habs : |tan θ * v| ≤ θ := abs_le.mpr ⟨hlo, hhi⟩
  have hcos := cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (tan θ * v)) hθ.2.le habs
  rw [cos_abs] at hcos
  exact sub_nonneg.mpr hcos

/-- Nonnegativity holds on the entire kernel support, without numerical approximations. -/
theorem kadiriKernel_nonneg {u : ℝ} (hu : u ∈ Icc 0 (kadiriSupport θ)) :
    0 ≤ kadiriKernel θ u := by
  have hu' : u ≤ -θ / tan θ - θ / tan θ := by
    calc
      u ≤ kadiriSupport θ := hu.2
      _ = _ := by unfold kadiriSupport; ring
  rw [kadiriKernel_eq_cosineCorrelation hθ]
  apply mul_nonneg (by positivity)
  apply intervalIntegral.integral_nonneg (by linarith)
  intro v hv
  apply mul_nonneg
  · exact kadiri_cosineBump_nonneg hθ ⟨hv.1, by linarith [hu.1, hv.2]⟩
  · exact kadiri_cosineBump_nonneg hθ ⟨by linarith [hu.1, hv.1], by linarith [hv.2]⟩

end

end PrimeFactorUnimodality
