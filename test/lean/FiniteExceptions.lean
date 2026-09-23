import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.FiniteExceptions

/-! # Exact interfaces and boundary cases for the complete horizontal tail -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

example {f f' : ℝ → ℝ} (s : Finset ℝ)
    {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ s → HasDerivAt f (f' x) x)
    (hi : IntervalIntegrable f' volume a b) :
    (∫ x in a..b, f' x) = f b - f a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_off_finset s hab hc hd hi

example {a b : ℝ} (hab : a ≤ b)
    (hi : IntervalIntegrable (fun x : ℝ => (SignType.sign x : ℝ)) volume a b) :
    (∫ x in a..b, (SignType.sign x : ℝ)) = |b| - |a| := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_off_finset {0} hab continuous_abs.continuousOn
  · intro x _ hx
    exact hasDerivAt_abs (by simpa using hx)
  · exact hi

example (a : ℝ) : (∫ x in a..a, (2 : ℝ) * x) = a ^ 2 - a ^ 2 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_off_finset {a} le_rfl
    (by fun_prop)
  · intro x hx _
    exact (lt_asymm hx.1 hx.2).elim
  · exact (by fun_prop : Continuous (fun x : ℝ => 2 * x)).intervalIntegrable _ _

end

end PrimeFactorUnimodality.Tests
