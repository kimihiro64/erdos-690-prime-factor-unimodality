import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.Analysis.Meromorphic.HorizontalFactorization

/-! # Exact interfaces and boundary cases for the complete horizontal tail -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

example {f : ℂ → ℂ} {K : Set ℂ}
    (hf : MeromorphicOn f K) (hK : IsCompact K)
    (horder : ∀ z : K, meromorphicOrderAt f z ≠ ⊤) :
    ∃ (s : Finset ℂ) (n : ℂ → ℤ) (g : ℂ → ℝ), ContinuousOn g K ∧
      ∀ a b t : ℝ, (∀ x ∈ uIcc a b, (x : ℂ) + t * I ∈ K) →
        (∫ x in a..b, Real.log ‖f ((x : ℂ) + t * I)‖) =
          (∑ w ∈ s, (n w : ℝ) * ∫ x in a..b, Real.log ‖(x : ℂ) + t * I - w‖) +
            ∫ x in a..b, g ((x : ℂ) + t * I) := by
  exact MeromorphicOn.exists_horizontal_log_integral_factorization hf hK horder



end

end PrimeFactorUnimodality.Tests
