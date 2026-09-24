import PrimeFactorUnimodality.Helpers.FiniteCertificates.DusartTailThetaPrefix

set_option autoImplicit false

/-! # Tail theta bounds from the single published theta-error ray

The bounded prefix is supplied by the checked count/log trace. The same
unbounded error estimate already used for prime counts and short intervals
supplies the remaining selected-prime theta inequalities above the cutoff.
-/

namespace PrimeFactorUnimodality

theorem hasTailThetaBounds_of_logSquared_ray
    (error : HasThetaLogSquaredError (1 / 5) 3594641) : HasTailThetaBounds :=
  hasTailThetaBounds_of_logSquared dusart_tail_theta_prefix error

end PrimeFactorUnimodality
