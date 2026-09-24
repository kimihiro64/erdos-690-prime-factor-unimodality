/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Measurability of Gamma

The reciprocal Gamma function is entire. Inverting it gives global
measurability, including Mathlib's value at the poles.
-/

namespace Complex

/-- Gamma is measurable on the entire complex plane. -/
@[fun_prop]
theorem measurable_Gamma : Measurable Gamma := by
  have h : Measurable (fun s : ℂ => ((Gamma s)⁻¹)⁻¹) :=
    differentiable_one_div_Gamma.continuous.measurable.inv
  simpa only [inv_inv] using h

end Complex
