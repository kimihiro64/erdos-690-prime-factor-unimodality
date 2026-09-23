/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Meromorphic.HorizontalFactorization

/-! # Continuity of meromorphic logarithmic integrals on horizontal rectangles

Finite factorization separates all logarithmic singularities. Each singular
integral is continuous through its zero height; the remaining continuous
integrand is extended by clipping both rectangle coordinates. The argument
allows zeros and poles on the segment and at either endpoint.
-/

namespace MeromorphicOn

noncomputable section

open Complex MeasureTheory Set

private theorem continuousOn_horizontal_integral {g : ℂ → ℝ} {K : Set ℂ}
    (hg : ContinuousOn g K) {a b c d : ℝ} (hcd : c ≤ d)
    (hrect : ∀ t ∈ Icc c d, ∀ x ∈ uIcc a b, (x : ℂ) + t * I ∈ K) :
    ContinuousOn (fun t : ℝ => ∫ x in a..b, g ((x : ℂ) + t * I)) (Icc c d) := by
  let F : ℝ → ℝ → ℝ := fun t x =>
    g ((max (min a b) (min (max a b) x) : ℝ) +
      (max c (min d t) : ℝ) * (I : ℂ))
  have hc : Continuous F.uncurry := by
    apply hg.comp_continuous (by fun_prop)
    intro p
    apply hrect
    · exact ⟨le_max_left _ _, max_le hcd (min_le_left _ _)⟩
    · exact ⟨le_max_left _ _, max_le min_le_max (min_le_left _ _)⟩
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := (volume : Measure ℝ)) hc a b).continuousOn.congr
  intro t ht
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp [F]
  rw [min_eq_right hx.2, max_eq_right hx.1, min_eq_right ht.2, max_eq_right ht.1]

/-- On a compact meromorphic rectangle, horizontal log-modulus integrals are continuous in height. -/
theorem continuousOn_integral_log_norm_horizontal {f : ℂ → ℂ} {K : Set ℂ}
    (hf : MeromorphicOn f K) (hK : IsCompact K)
    (horder : ∀ z : K, meromorphicOrderAt f z ≠ ⊤)
    {a b c d : ℝ} (hcd : c ≤ d)
    (hrect : ∀ t ∈ Icc c d, ∀ x ∈ uIcc a b, (x : ℂ) + t * I ∈ K) :
    ContinuousOn (fun t : ℝ => ∫ x in a..b, Real.log ‖f ((x : ℂ) + t * I)‖)
      (Icc c d) := by
  obtain ⟨s, n, g, hg, he⟩ := hf.exists_horizontal_log_integral_factorization hK horder
  have hc : Continuous (fun t : ℝ =>
      ∑ w ∈ s, (n w : ℝ) * ∫ x in a..b, Real.log ‖(x : ℂ) + t * I - w‖) :=
    continuous_finsetSum _ (fun w _ => continuous_const.mul
      (continuous_integral_log_norm_horizontal_sub w a b))
  exact (hc.continuousOn.add (continuousOn_horizontal_integral hg hcd hrect)).congr
    (fun t ht => he a b t (hrect t ht))

end

end MeromorphicOn
