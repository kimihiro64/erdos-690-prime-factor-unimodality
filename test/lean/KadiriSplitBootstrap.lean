import PrimeFactorUnimodality.Helpers.Analytic.KadiriSplitBootstrap

/-! # Single-crossing transforms and sharp bootstrap regressions

Test nonmonotone functions, a genuine sign-changing source, crossings
outside the integration interval, zero-length intervals, and exact
signed-transform endpoint values. Numerical region inputs are not asserted.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real Set

example {l r w : ℝ} (hw : w ∈ Icc l r) : min (-(l ^ 2)) (-(r ^ 2)) ≤ -(w ^ 2) := by
  apply min_endpoints_le_of_deriv_nonpos_persistent
    (fun x => ((hasDerivAt_id x).pow 2).neg) _ hw
  intro x y hxy hx
  dsimp at hx ⊢
  nlinarith only [hxy, hx]

example (a : ℝ) {l r w : ℝ} (hw : w ∈ Icc l r) : min a a ≤ a :=
  min_endpoints_le_of_deriv_nonpos_persistent (fun x => hasDerivAt_const x a)
    (fun _ _ _ _ => le_rfl) hw

example (f : ℝ → ℝ) (w : ℝ) : finiteExpTransform f 0 w = 0 := by
  simp [finiteExpTransform]

example (d w : ℝ) : finiteExpTransform (fun _ => 0) d w = 0 := by
  simp [finiteExpTransform]

example {f : ℝ → ℝ} {d : ℝ} (hf : ContinuousOn f (uIcc 0 d)) (w : ℝ) :
    HasDerivAt (finiteExpTransform f d) (finiteExpTransform (fun u => u * f u) d w) w :=
  hasDerivAt_finiteExpTransform hf w

example {x y : ℝ} (hxy : x ≤ y) :
    finiteExpTransform (fun u => 1 - u) 2 y ≤
      exp ((y - x) * 1) * finiteExpTransform (fun u => 1 - u) 2 x := by
  apply finiteExpTransform_le_exp_mul_of_singleCrossing (by norm_num)
    (by fun_prop) _ _ hxy
  · intro u _ hu
    linarith
  · intro u _ hu
    linarith

example {l r w : ℝ} (hw : w ∈ Icc l r) :
    min (finiteExpTransform (fun u => 1 - u) 2 l)
      (finiteExpTransform (fun u => 1 - u) 2 r) ≤ finiteExpTransform (fun u => 1 - u) 2 w := by
  apply min_finiteExpTransform_endpoints_le (c := 1) (by norm_num) (by fun_prop) _ _ hw
  · intro u _ hu
    linarith
  · intro u _ hu
    linarith

example {l r w : ℝ} (hw : w ∈ Icc l r) :
    min (finiteExpTransform (fun _ => (-1 : ℝ)) 2 l)
      (finiteExpTransform (fun _ => (-1 : ℝ)) 2 r) ≤
        finiteExpTransform (fun _ => (-1 : ℝ)) 2 w := by
  apply min_finiteExpTransform_endpoints_le (c := -1) (by norm_num) (by fun_prop) _ _ hw
  · intro u hu huc
    have := hu.1
    linarith
  · intro u _ _
    norm_num

example {l r w : ℝ} (hw : w ∈ Icc l r) :
    min (finiteExpTransform (fun _ => (1 : ℝ)) 2 l)
      (finiteExpTransform (fun _ => (1 : ℝ)) 2 r) ≤
        finiteExpTransform (fun _ => (1 : ℝ)) 2 w := by
  apply min_finiteExpTransform_endpoints_le (c := 3) (by norm_num) (by fun_prop) _ _ hw
  · intro u _ _
    norm_num
  · intro u hu hcu
    have := hu.2
    linarith

example {θ a₀ a₁ l r w : ℝ} (hθ : π / 2 < θ ∧ θ < π)
    (h₀ : 0 < a₀) (h₁ : 0 < a₁) (hw : w ∈ Icc l r) :
    min (kadiriTransformGap θ a₀ a₁ l) (kadiriTransformGap θ a₀ a₁ r) ≤
      kadiriTransformGap θ a₀ a₁ w := min_kadiriTransformGap_endpoints_le hθ h₀ h₁ hw

example {θ a₀ a₁ l r w : ℝ} (hθ : π / 2 < θ ∧ θ < π)
    (h₀ : 0 < a₀) (h₁ : 0 < a₁) (hw : w ∈ Icc l r) :
    min (kadiriTransformGapClosedForm θ a₀ a₁ l) (kadiriTransformGapClosedForm θ a₀ a₁ r) ≤
      kadiriTransformGapClosedForm θ a₀ a₁ w := by
  simpa only [kadiriTransformGap_eq_closedForm hθ] using
    min_kadiriTransformGap_endpoints_le hθ h₀ h₁ hw

example {θ a₀ a₁ w : ℝ} (hθ : π / 2 < θ ∧ θ < π) (h₀ : 0 < a₀) (h₁ : 0 < a₁) :
    min (kadiriTransformGap θ a₀ a₁ w) (kadiriTransformGap θ a₀ a₁ w) ≤
      kadiriTransformGap θ a₀ a₁ w := min_kadiriTransformGap_endpoints_le hθ h₀ h₁ ⟨le_rfl, le_rfl⟩

example {θ a₀ a₁ l r : ℝ} (hθ : π / 2 < θ ∧ θ < π)
    (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁) (hlr : l ≤ r) :
    a₁ * kadiriKernelExpIntegral θ (l - 1) - a₀ * kadiriKernelExpIntegral θ r ≤
      min (kadiriTransformGap θ a₀ a₁ l) (kadiriTransformGap θ a₀ a₁ r) :=
  kadiri_separate_transform_bound_le_endpoint_minimum hθ h₀ h₁ hlr

end

end PrimeFactorUnimodality.Tests
