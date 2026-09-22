/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePair

/-! # Derivative and decay of the reciprocal-square pair

The explicit negative derivative is the weight used in counting-function
Abel integrals. The pair tends to zero at infinity for every real shift.
-/

namespace Real

open Filter
open scoped Topology

/-- Derivative of the pair away from both poles. -/
theorem hasDerivAt_reciprocalSquarePair {t x : ℝ} (hm : x - t ≠ 0) (hp : x + t ≠ 0) :
    HasDerivAt (reciprocalSquarePair t) (-(2 / (x - t) ^ 3 + 2 / (x + t) ^ 3)) x := by
  have h := ((hasDerivAt_const x (1 : ℝ)).div (((hasDerivAt_id x).sub_const t).pow 2)
    (pow_ne_zero _ hm)).add
    ((hasDerivAt_const x (1 : ℝ)).div (((hasDerivAt_id x).add_const t).pow 2)
      (pow_ne_zero _ hp))
  convert h using 1
  · funext y
    rfl
  · simp only [Pi.pow_apply, id_eq]
    field_simp [hm, hp]
    ring

/-- Both inverse-square kernels vanish at infinity, with no restriction on the shift. -/
theorem tendsto_reciprocalSquarePair_atTop (t : ℝ) :
    Tendsto (reciprocalSquarePair t) atTop (𝓝 0) := by
  have h (c : ℝ) : Tendsto (fun x : ℝ => 1 / (x + c) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
      (tendsto_atTop_add_const_right atTop c tendsto_id))
  convert (h (-t)).add (h t) using 1
  · funext x
    simp only [reciprocalSquarePair, sub_eq_add_neg]
  · simp

end Real
