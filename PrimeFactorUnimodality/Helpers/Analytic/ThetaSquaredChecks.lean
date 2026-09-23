import PrimeFactorUnimodality.Helpers.Analytic.ThetaSquaredChain

/-! # Executable coverage checks for lower-band theta chains

Only adjacent rational margins are tested. The final endpoint is checked by
its fields rather than assumed, and the existing chain assembler supplies
the bound throughout the whole real interval.
-/

namespace PrimeFactorUnimodality.ThetaSquaredCheckpoint

/-- A linear adjacent-margin check, with explicit first and final checkpoints. -/
def checkFrom (c : ℚ) (p q : ThetaSquaredCheckpoint) : List ThetaSquaredCheckpoint → Bool
  | [] => decide (p.point = q.point ∧ p.lower = q.lower ∧ p.upper = q.upper ∧
      p.logUpper = q.logUpper ∧ Step c p p)
  | next :: rest => decide (Step c p next) && checkFrom c next q rest

/-- Accepted rational margins give exactly the original ordered coverage chain. -/
theorem chain_of_checkFrom {c : ℚ} {p q : ThetaSquaredCheckpoint}
    {points : List ThetaSquaredCheckpoint} (h : checkFrom c p q points = true) :
    Chain c p q (p :: points) := by
  induction points generalizing p with
  | nil =>
    simp only [checkFrom, decide_eq_true_eq] at h
    have hpq : p = q := by
      cases p
      cases q
      simp_all
    subst q
    exact Chain.single p h.2.2.2.2
  | cons next rest ih =>
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    exact Chain.cons p h.1 (ih h.2)

/-- A checked chain and valid retained endpoints bound every real point in its closed interval. -/
theorem bound_of_checkFrom {c : ℚ} (hc : 0 ≤ c) {p q : ThetaSquaredCheckpoint}
    {points : List ThetaSquaredCheckpoint} (h : checkFrom c p q points = true)
    (hvalid : ∀ r ∈ p :: points, r.Valid) {x : ℝ}
    (hpx : (p.point : ℝ) ≤ x) (hxq : x ≤ q.point) :
    |Chebyshev.theta x - x| ≤ (c : ℝ) * x / Real.log x ^ 2 :=
  (chain_of_checkFrom h).bound hc hvalid hpx hxq

end PrimeFactorUnimodality.ThetaSquaredCheckpoint
