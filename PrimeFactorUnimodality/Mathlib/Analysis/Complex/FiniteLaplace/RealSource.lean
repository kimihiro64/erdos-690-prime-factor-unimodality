/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Bounds

/-! # Conjugation and half-plane boundedness of finite Laplace transforms

Real sources commute with conjugation. A continuous source on a compact
nonnegative interval gives a uniform bound on the entire closed right
half-plane, including its imaginary boundary.
-/

namespace Complex

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

/-- The transform of a real source commutes with complex conjugation. -/
theorem finiteLaplace_conj_real (f : ℝ → ℝ) (d : ℝ) (s : ℂ) :
    finiteLaplace (fun t => (f t : ℂ)) d (conj s) =
      conj (finiteLaplace (fun t => (f t : ℂ)) d s) := by
  rw [finiteLaplace, finiteLaplace, ← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [map_mul, ← exp_conj, map_neg, conj_ofReal]

/-- Compact interval continuity gives a uniform bound on the closed right half-plane. -/
theorem exists_bound_finiteLaplace_rightHalfPlane {f : ℝ → ℂ} {d : ℝ}
    (hd : 0 ≤ d) (hf : ContinuousOn f (Icc 0 d)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, 0 ≤ s.re → ‖finiteLaplace f d s‖ ≤ M := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨max 0 B * d, mul_nonneg (le_max_left _ _) hd, ?_⟩
  intro s hs
  have h := norm_finiteLaplace_le_exp hd (le_max_left 0 B)
    (fun t ht => (hB t ht).trans (le_max_right 0 B)) s
  simpa only [max_eq_left (neg_nonpos.mpr hs), zero_mul, Real.exp_zero, mul_one] using h

end

end Complex
