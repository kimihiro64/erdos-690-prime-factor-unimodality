import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! # Exact interfaces and boundary regressions for counting normalization -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter Set
open MeasureTheory

example
    {F F' : ℝ → ℝ → ℝ} {a b t r : ℝ} (hr : 0 < r)
    (hF : ContinuousOn (Function.uncurry F) (Icc (t - r) (t + r) ×ˢ uIcc a b))
    (hF' : ContinuousOn (Function.uncurry F') (Icc (t - r) (t + r) ×ˢ uIcc a b))
    (hd : ∀ u ∈ Ioo (t - r) (t + r), ∀ x ∈ uIcc a b,
      HasDerivAt (fun v => F v x) (F' u x) u) :
    HasDerivAt (fun u => ∫ x in a..b, F u x) (∫ x in a..b, F' t x) t := by
  exact intervalIntegral.hasDerivAt_integral_of_continuousOn_rectangle hr hF hF' hd

example (a b t : ℝ) : HasDerivAt (fun u : ℝ => ∫ x in a..b, u * x)
    (∫ x in a..b, x) t := by
  apply intervalIntegral.hasDerivAt_integral_of_continuousOn_rectangle
    (F := fun u x => u * x) (F' := fun _ x => x) (r := 1) (by norm_num)
  · fun_prop
  · fun_prop
  · intro u _ x _
    simpa using (hasDerivAt_id u).mul_const x

example (t : ℝ) : HasDerivAt (fun u : ℝ => ∫ x in (1 : ℝ)..0, u * x)
    (∫ x in (1 : ℝ)..0, x) t := by
  apply intervalIntegral.hasDerivAt_integral_of_continuousOn_rectangle
    (F := fun u x => u * x) (F' := fun _ x => x) (r := 2) (by norm_num)
  · fun_prop
  · fun_prop
  · intro u _ x _
    simpa using (hasDerivAt_id u).mul_const x

example (t a : ℝ) : HasDerivAt (fun u : ℝ => ∫ x in a..a, u * x)
    (∫ x in a..a, x) t := by
  apply intervalIntegral.hasDerivAt_integral_of_continuousOn_rectangle
    (F := fun u x => u * x) (F' := fun _ x => x) (r := 1) (by norm_num)
  · fun_prop
  · fun_prop
  · intro u _ x _
    simpa using (hasDerivAt_id u).mul_const x

end

end PrimeFactorUnimodality.Tests
