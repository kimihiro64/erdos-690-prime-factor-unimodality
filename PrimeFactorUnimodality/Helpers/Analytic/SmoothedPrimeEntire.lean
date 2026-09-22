import Mathlib.NumberTheory.LSeries.Deriv
import PrimeFactorUnimodality.Helpers.Analytic.StechkinBasic

/-! # Entire dependence of the compactly smoothed prime sum

The support of the logarithmically sampled weight is finite, independently
of the complex parameter. Thus the smoothed von Mangoldt series is a
single finite sum of entire Dirichlet terms on the whole plane.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- Compact support of the smoothing weight makes the prime side entire. -/
theorem differentiable_smoothedVonMangoldt {f : ℝ → ℝ} {d : ℝ}
    (htail : ∀ u, d < u → f u = 0) : Differentiable ℂ (smoothedVonMangoldt f) := by
  classical
  let S : Finset ℕ := (hasFiniteSupport_log_weight htail).toFinset
  have heq : smoothedVonMangoldt f = fun s => ∑ n ∈ S, (f (Real.log n) : ℂ) *
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n := by
    funext s
    apply tsum_eq_sum
    intro n hn
    have hf : f (Real.log n) = 0 := by
      by_contra hf
      exact hn ((hasFiniteSupport_log_weight htail).mem_toFinset.mpr hf)
    simp [hf]
  rw [heq]
  apply Differentiable.fun_sum
  intro n _
  exact fun s => ((LSeries.hasDerivAt_term _ n s).differentiableAt).const_mul _

end

end PrimeFactorUnimodality
