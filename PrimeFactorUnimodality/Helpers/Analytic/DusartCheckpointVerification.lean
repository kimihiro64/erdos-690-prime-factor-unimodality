import PrimeFactorUnimodality.Helpers.Analytic.DusartCheckpointAnchors
import PrimeFactorUnimodality.Helpers.Analytic.DusartSquaredAtPublishedCutoff
import PrimeFactorUnimodality.Helpers.Analytic.DusartTuringVerification
import PrimeFactorUnimodality.Helpers.Analytic.ThetaSquaredChain

/-! # Exact Dusart consumers of shared lower-band checkpoints

The lower band and both prime-counting anchors are derived from endpoint
enclosures and rational comparisons. These are genuine finite inputs: this
module does not supply their numerical data or claim the closed providers.
The upper analytic ray reuses the already proved Turing and region bootstrap.
-/

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-- A compact checkpoint chain supplies exactly the published lower-theta-band obligation. -/
theorem thetaLogSquared_on_published_band_of_checkpoints
    {p q : ThetaSquaredCheckpoint} {points : List ThetaSquaredCheckpoint}
    (hpoints : ∀ r ∈ points, r.Valid)
    (hsteps : ThetaSquaredCheckpoint.Chain (1 / 5) p q points)
    (hp : p.point ≤ 3594641) (hq : 1441000000000 ≤ q.point) :
    ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2 := by
  intro x hx hX
  have hp' : (p.point : ℝ) ≤ 3594641 := by exact_mod_cast hp
  have hq' : (1441000000000 : ℝ) ≤ q.point := by exact_mod_cast hq
  simpa using hsteps.bound (by norm_num) hpoints (hp'.trans hx) (hX.trans hq')

/-- Checkpoint data removes the previously assumed whole lower-band inequality. -/
theorem hasThetaLogSquaredError_of_checkpoints_and_turing_rows
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
    HasThetaLogSquaredError (1 / 5) 3594641 :=
  hasThetaLogSquaredError_of_lower_band_and_turing_rows
    (thetaLogSquared_on_published_band_of_checkpoints hpoints hsteps hp hq)
    hrows hb hmargin hchain

/-- The prime-counting provider needs rational anchor tests instead of unproved real anchors. -/
theorem hasDusartPrimeCountingBounds_of_checkpoint_anchors
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
  apply hasDusartPrimeCountingBounds_of_published_logSquared finite error
  · simpa only [hpoint, Nat.cast_ofNat] using
      ThetaSquaredCheckpoint.lower_anchor hp hL0 hL hklo hlower
  · simpa only [hpoint, Nat.cast_ofNat] using
      ThetaSquaredCheckpoint.upper_anchor hp hL0 hL hkhi hupper

end

end PrimeFactorUnimodality
