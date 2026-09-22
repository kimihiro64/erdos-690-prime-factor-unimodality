/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Integrating a logarithmic derivative using a continuous logarithm

A continuous local lift through the complex exponential inherits the
derivative `f'/f` by Mathlib's inverse-derivative theorem. The fundamental
theorem of calculus then identifies the logarithmic-derivative integral
with the increment of any continuous logarithm, without branch-cut assumptions.
-/

open Filter Set
open scoped Topology

namespace Complex

/-- A continuous local logarithm is differentiable when its exponential is differentiable. -/
theorem hasDerivAt_logarithm {L f : ℝ → ℂ} {x : ℝ} {f' : ℂ}
    (hL : ContinuousAt L x) (hf : HasDerivAt f f' x)
    (he : (fun y => exp (L y)) =ᶠ[𝓝 x] f) :
    HasDerivAt L (f' / f x) x := by
  have hd := (hasDerivAt_exp (L x)).hasFDerivAt.restrictScalars ℝ
  have h := hd.of_comp_of_leftInverse hL hf.hasFDerivAt he
    (f'symm := ContinuousLinearMap.mul ℝ ℂ (exp (L x))⁻¹)
    (fun z => by simp [mul_left_comm])
  have hex : exp (L x) = f x := he.eq_of_nhds
  convert! h.hasDerivAt using 1
  simp [ContinuousLinearMap.mul_apply', div_eq_mul_inv, mul_comm, hex]

/-- The integral of `f'/f` equals the increment of any continuous logarithm of `f`. -/
theorem integral_div_eq_logarithm_sub {L f f' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hL : ContinuousOn L (Icc a b))
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (he : ∀ x ∈ Icc a b, exp (L x) = f x)
    (hi : IntervalIntegrable (fun x => f' x / f x) MeasureTheory.volume a b) :
    ∫ x in a..b, f' x / f x = L b - L a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hL ?_ hi
  intro x hx
  apply hasDerivAt_logarithm (hL.continuousAt (Icc_mem_nhds hx.1 hx.2)) (hf x hx)
  exact Filter.eventually_of_mem (Icc_mem_nhds hx.1 hx.2) (fun y hy => he y hy)

end Complex
