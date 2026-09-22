import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeight
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.CorrelationBound
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.CosineCorrelation

/-! # The sharp second-derivative bound for the paper weight

The second derivative is a negative multiple of a sine correlation.
The square-integral bound for correlations shows that its absolute value
on the entire support is at most its absolute value at zero. Thus the
maximum needed in the paper is determined symbolically, not sampled.
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

/-- Exact derivative-correlation identity, including its sign and normalization. -/
theorem kadiriKernel₂_eq_sineCorrelation (u : ℝ) :
    kadiriKernel₂ θ u = -(tan θ ^ 2 / cos θ ^ 4) *
      ∫ v in (θ / tan θ)..(-θ / tan θ - u),
        sin (tan θ * v) * sin (tan θ * (v + u)) := by
  have ht := (tan_neg hθ).ne
  have hs := (sin_pos hθ).ne'
  have hc := (cos_neg hθ).ne
  have hsec : 1 + tan θ ^ 2 = 1 / cos θ ^ 2 := by
    rw [tan_eq_sin_div_cos]
    field_simp
    nlinarith [sin_sq_add_cos_sq θ]
  rw [intervalIntegral.integral_sin_mul_sin_translate ht]
  have h₁ : 2 * tan θ * (-θ / tan θ - u) + tan θ * u = -(2 * θ + u * tan θ) := by
    field_simp
    ring
  have h₂ : 2 * tan θ * (θ / tan θ) + tan θ * u = 2 * θ + u * tan θ := by
    field_simp
  have hsin : sin (2 * θ + u * tan θ) + sin (u * tan θ) =
      2 * sin (θ + u * tan θ) * cos θ := by
    rw [sin_add_sin, show (2 * θ + u * tan θ + u * tan θ) / 2 = θ + u * tan θ by ring,
      show (2 * θ + u * tan θ - u * tan θ) / 2 = θ by ring]
  rw [h₁, h₂, Real.sin_neg, kadiriKernel₂, hsec, kadiriSupport,
    mul_comm (tan θ) u, tan_eq_sin_div_cos, sin_two_mul]
  rw [tan_eq_sin_div_cos] at hsin
  generalize sin (u * (sin θ / cos θ)) = S₀ at *
  generalize sin (θ + u * (sin θ / cos θ)) = S₁ at *
  generalize sin (2 * θ + u * (sin θ / cos θ)) = S₂ at *
  generalize cos (u * (sin θ / cos θ)) = C₀ at *
  field_simp
  linear_combination 8 * cos θ * hsin

/-- The full-support second-derivative norm is attained at zero. -/
theorem abs_kadiriKernel₂_le_neg_zero {u : ℝ} (hu : u ∈ Icc 0 (kadiriSupport θ)) :
    |kadiriKernel₂ θ u| ≤ -kadiriKernel₂ θ 0 := by
  have hrange : u ≤ -θ / tan θ - θ / tan θ := by
    calc
      u ≤ kadiriSupport θ := hu.2
      _ = _ := by unfold kadiriSupport; ring
  have hbound := intervalIntegral.abs_integral_mul_translate_le_integral_sq
    (f := fun v => sin (tan θ * v)) (by fun_prop) hu.1 hrange
  rw [kadiriKernel₂_eq_sineCorrelation hθ u, kadiriKernel₂_eq_sineCorrelation hθ 0]
  simp only [abs_mul, abs_neg, sub_zero, add_zero, ← sq]
  have hcoef : 0 ≤ tan θ ^ 2 / cos θ ^ 4 := by positivity
  rw [abs_of_nonneg hcoef, neg_mul, neg_neg]
  exact mul_le_mul_of_nonneg_left hbound hcoef

/-- The sharp unscaled bound is nonnegative. -/
theorem neg_kadiriKernel₂_zero_nonneg : 0 ≤ -kadiriKernel₂ θ 0 :=
  (abs_nonneg _).trans (abs_kadiriKernel₂_le_neg_zero hθ ⟨le_rfl, (kadiriSupport_pos hθ).le⟩)

/-- The exact maximum in the paper is attained at the left endpoint. -/
theorem isGreatest_abs_kadiriKernel₂ :
    IsGreatest ((fun u => |kadiriKernel₂ θ u|) '' Icc 0 (kadiriSupport θ))
      (-kadiriKernel₂ θ 0) := by
  refine ⟨⟨0, ⟨le_rfl, (kadiriSupport_pos hθ).le⟩, ?_⟩, ?_⟩
  · exact abs_of_nonpos (neg_nonneg.mp (neg_kadiriKernel₂_zero_nonneg hθ))
  · rintro _ ⟨u, hu, rfl⟩
    exact abs_kadiriKernel₂_le_neg_zero hθ hu

/-- A closed trigonometric expression for the sharp second-derivative constant. -/
theorem neg_kadiriKernel₂_zero_eq :
    -kadiriKernel₂ θ 0 = (tan θ ^ 2 / cos θ ^ 4) * (-θ / tan θ + cos θ ^ 2) := by
  have ht := (tan_neg hθ).ne
  have hs := (sin_pos hθ).ne'
  have hc := (cos_neg hθ).ne
  rw [kadiriKernel₂_eq_sineCorrelation hθ 0,
    intervalIntegral.integral_sin_mul_sin_translate ht]
  simp only [sub_zero, add_zero, mul_zero, cos_zero, mul_one, neg_mul, neg_neg]
  have h₁ : 2 * tan θ * (-θ / tan θ) = -(2 * θ) := by field_simp
  have h₂ : 2 * tan θ * (θ / tan θ) = 2 * θ := by field_simp
  rw [h₁, h₂, Real.sin_neg, sin_two_mul, tan_eq_sin_div_cos]
  field_simp
  ring

/-- The exact cubic scaling of the sharp bound used by the explicit formula. -/
theorem norm_kadiriWeight₂_le {η u : ℝ} (hη : 0 < η)
    (hu : u ∈ Icc 0 (kadiriWeightSupport θ η)) :
    ‖(kadiriWeight₂ θ η u : ℂ)‖ ≤ η ^ 3 * (-kadiriKernel₂ θ 0) := by
  have hu' : η * u ∈ Icc 0 (kadiriSupport θ) := by
    refine ⟨mul_nonneg hη.le hu.1, ?_⟩
    simpa only [mul_comm] using (le_div_iff₀ hη).mp hu.2
  rw [Complex.norm_real, Real.norm_eq_abs, kadiriWeight₂, abs_mul,
    abs_of_nonneg (pow_nonneg hη.le 3)]
  exact mul_le_mul_of_nonneg_left (abs_kadiriKernel₂_le_neg_zero hθ hu') (pow_nonneg hη.le 3)

end

end PrimeFactorUnimodality
