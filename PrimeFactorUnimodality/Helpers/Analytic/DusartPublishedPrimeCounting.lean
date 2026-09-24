import PrimeFactorUnimodality.Helpers.Analytic.DusartPublishedAnchors
import PrimeFactorUnimodality.Helpers.FiniteCertificates.DusartPublishedPiPrefix
import PrimeFactorUnimodality.Helpers.FiniteCertificates.DusartPublishedPrimeCount

set_option autoImplicit false

/-! # Prime-counting bounds from the single published theta-error ray

The finite real-variable prefix and exact endpoint count are discharged by
compact checked rows. Both Abel anchors follow from the same theta estimate;
only that unbounded analytic estimate remains a premise of this provider.
-/

namespace PrimeFactorUnimodality

theorem hasDusartPrimeCountingBounds_of_logSquared_ray
    (error : HasThetaLogSquaredError (1 / 5) 3594641) : HasDusartPrimeCountingBounds :=
  hasDusartPrimeCountingBounds_of_published_logSquared_count
    dusart_published_prime_count dusart_published_primeCountingPrefix error

end PrimeFactorUnimodality
