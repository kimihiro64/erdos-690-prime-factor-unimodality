import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Group.Bounded
import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeightEndpoints

/-! # The scaled compact smoothing weight of the paper

The weight is exactly `eta*h_theta(eta*u)` on its closed support and zero
elsewhere. Its interval derivatives and endpoints are proved directly,
without requiring a continuous extension across zero. Compactness gives
an actual bound for its second derivative; a sharp numerical value of
that bound and positivity of the Laplace transform are separate tasks.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real Set
open scoped Topology

/-- The scaled support endpoint. -/
def kadiriWeightSupport (θ η : ℝ) : ℝ := kadiriSupport θ / η

/-- The paper's compact weight, including its zero extension. -/
def kadiriWeight (θ η u : ℝ) : ℝ :=
  if u ∈ Icc 0 (kadiriWeightSupport θ η) then η * kadiriKernel θ (η * u) else 0

/-- The interval first derivative of the scaled weight. -/
def kadiriWeight₁ (θ η u : ℝ) : ℝ := η ^ 2 * kadiriKernel₁ θ (η * u)

/-- The interval second derivative of the scaled weight. -/
def kadiriWeight₂ (θ η u : ℝ) : ℝ := η ^ 3 * kadiriKernel₂ θ (η * u)

/-- On the closed support the defining rescaling is exact. -/
theorem kadiriWeight_of_mem {θ η u : ℝ} (hu : u ∈ Icc 0 (kadiriWeightSupport θ η)) :
    kadiriWeight θ η u = η * kadiriKernel θ (η * u) := by simp [kadiriWeight, hu]

/-- The weight is zero beyond its support. -/
theorem kadiriWeight_tail (θ η u : ℝ) (hu : kadiriWeightSupport θ η < u) :
    kadiriWeight θ η u = 0 := by simp [kadiriWeight, not_le.mpr hu]

/-- The scaled weight is continuous on its actual integration interval. -/
theorem continuousOn_kadiriWeight (θ η : ℝ) :
    ContinuousOn (kadiriWeight θ η) (Icc 0 (kadiriWeightSupport θ η)) := by
  have hc : Continuous (fun u : ℝ => η * kadiriKernel θ (η * u)) :=
    continuous_const.mul ((continuous_kadiriKernel θ).comp (continuous_const.mul continuous_id))
  apply hc.continuousOn.congr
  intro u hu
  exact kadiriWeight_of_mem hu

/-- Continuity of the interval first derivative. -/
theorem continuous_kadiriWeight₁ (θ η : ℝ) : Continuous (kadiriWeight₁ θ η) :=
  continuous_const.mul ((continuous_kadiriKernel₁ θ).comp (continuous_const.mul continuous_id))

/-- Continuity of the interval second derivative. -/
theorem continuous_kadiriWeight₂ (θ η : ℝ) : Continuous (kadiriWeight₂ θ η) :=
  continuous_const.mul ((continuous_kadiriKernel₂ θ).comp (continuous_const.mul continuous_id))

/-- On the interior, the clipped weight has the stated interval derivative. -/
theorem hasDerivAt_kadiriWeight {θ η u : ℝ} (hu : u ∈ Ioo 0 (kadiriWeightSupport θ η)) :
    HasDerivAt (kadiriWeight θ η) (kadiriWeight₁ θ η u) u := by
  have h := ((hasDerivAt_kadiriKernel θ (η * u)).comp u
    ((hasDerivAt_id u).const_mul η)).const_mul η
  have h' : HasDerivAt (fun v => η * kadiriKernel θ (η * v)) (kadiriWeight₁ θ η u) u := by
    convert h using 1
    · rfl
    · dsimp [kadiriWeight₁]
      ring
  apply h'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact kadiriWeight_of_mem ⟨hv.1.le, hv.2.le⟩

/-- Differentiation of the first derivative has the exact cubic scaling factor. -/
theorem hasDerivAt_kadiriWeight₁ (θ η u : ℝ) :
    HasDerivAt (kadiriWeight₁ θ η) (kadiriWeight₂ θ η u) u := by
  have h := ((hasDerivAt_kadiriKernel₁ θ (η * u)).comp u
    ((hasDerivAt_id u).const_mul η)).const_mul (η ^ 2)
  convert h using 1
  · rfl
  · dsimp [kadiriWeight₂]
    ring

/-- Compactness supplies a genuine second-derivative bound for the explicit formula. -/
theorem exists_bound_kadiriWeight₂ (θ η : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ Icc 0 (kadiriWeightSupport θ η),
      ‖(kadiriWeight₂ θ η u : ℂ)‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Complex.continuous_ofReal.comp (continuous_kadiriWeight₂ θ η)).continuousOn
  exact ⟨max 0 M, le_max_left _ _, fun u hu => (hM u hu).trans (le_max_right _ _)⟩

variable {θ η : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)

include hθ hη

/-- The scaled support length is strictly positive. -/
theorem kadiriWeightSupport_pos : 0 < kadiriWeightSupport θ η :=
  div_pos (kadiriSupport_pos hθ) hη

/-- The scaled endpoint value is exactly `eta*g_1(theta)`. -/
theorem kadiriWeight_zero : kadiriWeight θ η 0 =
    η * ((1 + tan θ ^ 2) * (3 - θ * tan θ - 3 * θ / tan θ)) := by
  rw [kadiriWeight_of_mem ⟨le_rfl, (kadiriWeightSupport_pos hθ hη).le⟩,
    mul_zero, kadiriKernel_zero hθ]

/-- Every positive scale gives a genuinely nonzero paper weight. -/
theorem kadiriWeight_zero_pos : 0 < kadiriWeight θ η 0 := by
  rw [kadiriWeight_of_mem ⟨le_rfl, (kadiriWeightSupport_pos hθ hη).le⟩, mul_zero]
  exact mul_pos hη (kadiriKernel_zero_pos hθ)

/-- The scaled weight vanishes at its right endpoint. -/
theorem kadiriWeight_support : kadiriWeight θ η (kadiriWeightSupport θ η) = 0 := by
  rw [kadiriWeight_of_mem ⟨(kadiriWeightSupport_pos hθ hη).le, le_rfl⟩]
  rw [kadiriWeightSupport, mul_div_cancel₀ _ hη.ne', kadiriKernel_support hθ, mul_zero]

omit hη in
/-- The first interval derivative vanishes at zero. -/
theorem kadiriWeight₁_zero : kadiriWeight₁ θ η 0 = 0 := by
  simp [kadiriWeight₁, kadiriKernel₁_zero hθ]

/-- The first interval derivative vanishes at the scaled right endpoint. -/
theorem kadiriWeight₁_support : kadiriWeight₁ θ η (kadiriWeightSupport θ η) = 0 := by
  rw [kadiriWeight₁, kadiriWeightSupport, mul_div_cancel₀ _ hη.ne',
    kadiriKernel₁_support hθ, mul_zero]

/-- The second interval derivative also vanishes at the scaled right endpoint. -/
theorem kadiriWeight₂_support : kadiriWeight₂ θ η (kadiriWeightSupport θ η) = 0 := by
  rw [kadiriWeight₂, kadiriWeightSupport, mul_div_cancel₀ _ hη.ne',
    kadiriKernel₂_support hθ, mul_zero]

end

end PrimeFactorUnimodality
