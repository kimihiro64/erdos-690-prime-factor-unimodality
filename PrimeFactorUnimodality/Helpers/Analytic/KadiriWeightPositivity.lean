import PrimeFactorUnimodality.Helpers.Analytic.KadiriCorrelation
import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeight

/-! # Nonnegativity of the actual scaled compact weight

The cosine-correlation proof applies throughout the unscaled support;
positive rescaling and the zero extension preserve nonnegativity.
-/

namespace PrimeFactorUnimodality

open Real Set

/-- The paper's actual compact weight is nonnegative at every real argument. -/
theorem kadiriWeight_nonneg {θ η : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)
    (u : ℝ) : 0 ≤ kadiriWeight θ η u := by
  unfold kadiriWeight
  split_ifs with hu
  · apply mul_nonneg hη.le
    apply kadiriKernel_nonneg hθ
    refine ⟨mul_nonneg hη.le hu.1, ?_⟩
    have h := (le_div_iff₀ hη).mp hu.2
    simpa only [mul_comm] using h
  · exact le_rfl

end PrimeFactorUnimodality
