/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Differentiability
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.RealSource
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.PhragmenLindelof.RealPart

/-! # Reflected finite Laplace comparisons across a vertical strip

The compact source gives the entire continuation and uniform half-plane
bound needed to extend a comparison from one strip edge. No growth or
interior positivity assumption on the transform is needed.
-/

namespace Complex

open Set

/-- A boundary comparison for a finite transform extends to every point of the closed strip. -/
theorem re_finiteLaplace_reflected_pair_nonneg {f : ℝ → ℂ} {d r δ κ : ℝ}
    (hd : 0 ≤ d) (hf : ContinuousOn f (Icc 0 d)) (hr : 0 < r) (hδ : 0 ≤ δ)
    (hboundary : ∀ z : ℂ, z.re = 0 →
      0 ≤ (finiteLaplace f d z + finiteLaplace f d ((r : ℂ) - z) -
        (κ : ℂ) * (finiteLaplace f d (z + δ) +
          finiteLaplace f d ((r : ℂ) - z + δ))).re)
    {z : ℂ} (hz₀ : 0 ≤ z.re) (hzr : z.re ≤ r) :
    0 ≤ (finiteLaplace f d z + finiteLaplace f d ((r : ℂ) - z) -
      (κ : ℂ) * (finiteLaplace f d (z + δ) +
        finiteLaplace f d ((r : ℂ) - z + δ))).re := by
  obtain ⟨M, _, hM⟩ := exists_bound_finiteLaplace_rightHalfPlane hd hf
  exact re_reflected_pair_nonneg_of_boundary hr hδ
    (differentiable_finiteLaplace (by simpa only [uIcc_of_le hd] using hf))
    hM hboundary hz₀ hzr

end Complex
