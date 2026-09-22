import PrimeFactorUnimodality.Helpers.Analytic.DusartProofPart04
import PrimeFactorUnimodality.Helpers.Analytic.DusartRootBounds

set_option autoImplicit false

/-! # Dusart finite-range consequences

These consequences combine the separately checked analytic estimates with
the fixed finite computations in the preceding parts.
-/

namespace PrimeFactorUnimodality

noncomputable section

theorem dusart_proposition_3_2_of_uniform_strict_root_bound_all_closed
    (hroot : ∀ y : Real, 0 ≤ y →
      Chebyshev.psi y < (100007 : Real) / 100000 * y) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  intro x hx
  exact dusart_proposition_3_2_of_uniform_strict_root_bound_all
    (fun y hy hy64 => dusart_proposition_3_2_small_64 hy hy64) hroot x hx

theorem dusart_proposition_3_2_of_10m_lemma_and_theta_bounds
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  apply dusart_proposition_3_2_of_paper_lemma_and_theta_bounds
  · exact dusart_lemma_3_3_of_10m_intermediate_and_theta_upper
      (dusart_theta_upper_1000081_of_bounds thetaBounds)
  · exact thetaBounds

end

end PrimeFactorUnimodality
