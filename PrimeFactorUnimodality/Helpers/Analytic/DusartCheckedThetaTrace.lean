import PrimeFactorUnimodality.Helpers.Analytic.CheckedThetaPrimeTrace
import PrimeFactorUnimodality.Helpers.Analytic.DusartCheckpointVerification
import PrimeFactorUnimodality.Helpers.Analytic.ThetaSquaredChecks

/-! # The published lower theta band from checked compact prime blocks

Exact prime counts, prepared scalar arithmetic and rational transition and
coverage checks provide the whole lower band. This interface does not assume
theta enclosures, individual prime logarithms or real interval coverage.
The numerical block data and exact prime counts must still be supplied.
-/

namespace PrimeFactorUnimodality

open ThetaPrimeCheckpoint

/-- Compact count/log blocks and adjacent margins imply the complete published lower band. -/
theorem thetaLogSquared_on_published_band_of_checked_prime_trace
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
  have hvalid := squared_valid_of_checkTrace hc hs hcounts htrace hpositive
  exact thetaLogSquared_on_published_band_of_checkpoints
    hvalid (ThetaSquaredCheckpoint.chain_of_checkFrom hchain) hp hq

end PrimeFactorUnimodality
