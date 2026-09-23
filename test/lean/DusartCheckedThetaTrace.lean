import PrimeFactorUnimodality.Helpers.Analytic.DusartCheckedThetaTrace

/-! # Complete prime-block transitions and coverage regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open LeanCert.Core
open PrimeFactorUnimodality

open ThetaPrimeCheckpoint

example
    {c : SharedTaylorIntervals} (hc : c.Prepared)
    {start p q : ThetaPrimeCheckpoint} (hs : start.Valid)
    {points : List ThetaPrimeCheckpoint}
    (hcounts : ∀ s ∈ p :: points, Nat.primeCounting s.point = s.count)
    (htrace : checkTrace c start (p :: points) = true)
    (hpositive : ∀ s ∈ p :: points, 2 ≤ s.point ∧ 0 < s.log.hi)
    (hchain : ThetaSquaredCheckpoint.checkFrom (1 / 5) p.squared q.squared
      (points.map squared) = true)
    (hp : p.point ≤ 3594641) (hq : 1441000000000 ≤ q.point) :
    ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2 := by
  exact PrimeFactorUnimodality.thetaLogSquared_on_published_band_of_checked_prime_trace hc hs hcounts htrace hpositive hchain hp hq



end

end PrimeFactorUnimodality.Tests
