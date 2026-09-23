import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.DusartCheckpointVerification

/-! # Exact interfaces and real-interval checkpoint regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open PrimeFactorUnimodality.ThetaSquaredCheckpoint

example
    {p q : ThetaSquaredCheckpoint} {points : List ThetaSquaredCheckpoint}
    (hpoints : ∀ r ∈ points, r.Valid)
    (hsteps : ThetaSquaredCheckpoint.Chain (1 / 5) p q points)
    (hp : p.point ≤ 3594641) (hq : 1441000000000 ≤ q.point) :
    ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2 := by
  exact PrimeFactorUnimodality.thetaLogSquared_on_published_band_of_checkpoints hpoints hsteps hp hq

example
    {p q : ThetaSquaredCheckpoint} {points : List ThetaSquaredCheckpoint}
    (hpoints : ∀ r ∈ points, r.Valid)
    (hsteps : ThetaSquaredCheckpoint.Chain (1 / 5) p q points)
    (hp : p.point ≤ 3594641) (hq : 1441000000000 ≤ q.point)
    {n : ℕ} {rows : Fin n → XiSignRow} {b : ℚ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 +
      turingCountErrorBudget 1000000000 b <
        (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_of_checkpoints_and_turing_rows hpoints hsteps hp hq hrows hb hmargin hchain

example
    (finite : HasDusartRealPrimeCountingBoundsBelow 3594641)
    (error : HasThetaLogSquaredError (1 / 5) 3594641)
    {p : ThetaSquaredCheckpoint} (hp : p.Valid) (hpoint : p.point = 3594641)
    {L : ℚ} (hL0 : 0 ≤ L) (hL : (L : ℝ) ≤ Real.log p.point)
    {klo khi : ℕ} (hklo : klo ≤ Nat.primeCounting p.point)
    (hkhi : Nat.primeCounting p.point ≤ khi)
    (hlower : p.upper * p.logUpper ^ 2 + (p.point : ℚ) * p.logUpper +
      (1 / 5 : ℚ) * p.point ≤ (klo : ℚ) * L ^ 3)
    (hupper : (khi : ℚ) * p.logUpper ^ 3 ≤ p.lower * L ^ 2 +
      (6381 / 5000 : ℚ) * p.point * L - (1 / 5 : ℚ) * p.point) :
    HasDusartPrimeCountingBounds := by
  exact PrimeFactorUnimodality.hasDusartPrimeCountingBounds_of_checkpoint_anchors finite error hp hpoint hL0 hL hklo hkhi hlower hupper



end

end PrimeFactorUnimodality.Tests
