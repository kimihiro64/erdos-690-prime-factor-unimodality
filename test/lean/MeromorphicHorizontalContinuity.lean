import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.Analysis.Meromorphic.HorizontalContinuity

/-! # Exact interfaces and boundary cases for the complete horizontal tail -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

example {f : ℂ → ℂ} {K : Set ℂ}
    (hf : MeromorphicOn f K) (hK : IsCompact K)
    (horder : ∀ z : K, meromorphicOrderAt f z ≠ ⊤)
    {a b c d : ℝ} (hcd : c ≤ d)
    (hrect : ∀ t ∈ Icc c d, ∀ x ∈ uIcc a b, (x : ℂ) + t * I ∈ K) :
    ContinuousOn (fun t : ℝ => ∫ x in a..b, Real.log ‖f ((x : ℂ) + t * I)‖)
      (Icc c d) := by
  exact MeromorphicOn.continuousOn_integral_log_norm_horizontal hf hK horder hcd hrect



end

end PrimeFactorUnimodality.Tests
