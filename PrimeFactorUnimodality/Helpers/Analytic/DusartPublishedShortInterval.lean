import PrimeFactorUnimodality.Helpers.Analytic.DusartSquaredAtPublishedCutoff
import PrimeFactorUnimodality.Helpers.FiniteCertificates.DusartPublishedShortPrefix

set_option autoImplicit false

/-! # Short-interval primes from the single published theta-error ray

The full bounded prefix is supplied by compact checked sieve/log rows. The
existing theta-increment proof supplies every input above that prefix.
-/

namespace PrimeFactorUnimodality

theorem hasDusartShortIntervalPrime_of_logSquared_ray
    (error : HasThetaLogSquaredError (1 / 5) 3594641) : HasDusartShortIntervalPrime :=
  hasDusartShortIntervalPrime_of_published_logSquared
    dusart_published_shortIntervalPrefix error

end PrimeFactorUnimodality
