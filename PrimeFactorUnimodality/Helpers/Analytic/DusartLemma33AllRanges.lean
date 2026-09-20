import PrimeFactorUnimodality.Helpers.Analytic.DusartProof
import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33Midrange
import PrimeFactorUnimodality.Helpers.Analytic.DusartIntermediateLemma

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section

/- Global assembly of the three ranges used in Dusart's proof of Lemma 3.3:
   the published direct computation, the intermediate coefficient argument,
   and the analytic tail. -/
theorem dusart_lemma_3_3_all_ranges
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  intro x hx
  by_cases hlow : x ≤ (10 : Real) ^ 7
  · exact dusart_lemma_3_3_finite_through_10000000 x hx
      (by norm_num at hlow ⊢; exact hlow)
  · have hlo : (10 : Real) ^ 7 ≤ x := le_of_not_ge hlow
    by_cases hmid : x ≤ (10 : Real) ^ 33
    · exact dusart_lemma_3_3_intermediate hlo hmid theta_upper
    · have hcut : (10 ^ 11 : Real) ^ 3 ≤ x := by
        calc
          (10 ^ 11 : Real) ^ 3 = (10 : Real) ^ 33 := by
            norm_num [pow_mul]
          _ ≤ x := by
            norm_num at hmid ⊢
            linarith
      exact dusart_lemma_3_3_large hcut theta_upper


theorem dusart_lemma_3_3_all_ranges_of_theta_bounds
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_all_ranges
    (dusart_theta_upper_1000081_of_bounds thetaBounds)

end

end PrimeFactorUnimodality
