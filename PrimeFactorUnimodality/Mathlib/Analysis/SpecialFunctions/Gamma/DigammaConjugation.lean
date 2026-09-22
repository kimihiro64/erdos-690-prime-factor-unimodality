/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-! # Conjugation of the digamma function

Gamma commutes with conjugation, so the conjugation rule for derivatives
gives the same identity for its logarithmic derivative. The totalized
identity holds everywhere, including at the poles.
-/

namespace Complex

open scoped ComplexConjugate

/-- The gamma derivative commutes with complex conjugation, including its totalized values. -/
theorem deriv_Gamma_conj (z : ℂ) : deriv Gamma (conj z) = conj (deriv Gamma z) := by
  have heq : conj ∘ Gamma ∘ conj = Gamma := by
    funext w
    simp only [Function.comp_apply, Gamma_conj, starRingEnd_self_apply]
  have hd := congrFun (deriv_conj_conj (f := Gamma)) (conj z)
  simpa only [heq, Function.comp_apply, starRingEnd_self_apply] using hd

/-- Digamma commutes with complex conjugation. -/
theorem digamma_conj (z : ℂ) : digamma (conj z) = conj (digamma z) := by
  simp only [digamma_def, logDeriv_apply, deriv_Gamma_conj, Gamma_conj, map_div₀]

/-- The real part is the average of digamma at a point and its conjugate. -/
theorem ofReal_re_digamma_eq_average (z : ℂ) :
    ((digamma z).re : ℂ) = (digamma z + digamma (conj z)) / 2 := by
  rw [digamma_conj, add_conj]
  push_cast
  ring

end Complex
