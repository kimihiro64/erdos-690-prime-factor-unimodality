import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.ThetaSquaredChain

/-! # Exact interfaces and real-interval checkpoint regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open PrimeFactorUnimodality.ThetaSquaredCheckpoint

example {c : ℚ} {p q r : ThetaSquaredCheckpoint}
    {left right : List ThetaSquaredCheckpoint}
    (hl : Chain c p q left) (hr : Chain c q r right) :
    Chain c p r (left ++ right) := by
  exact PrimeFactorUnimodality.ThetaSquaredCheckpoint.Chain.append hl hr

example {c : ℚ} {p q : ThetaSquaredCheckpoint}
    {rows : List ThetaSquaredCheckpoint} (h : Chain c p q rows)
    {x : ℝ} (hpx : (p.point : ℝ) ≤ x) (hxq : x ≤ q.point) :
    ∃ u ∈ rows, ∃ v ∈ rows, Step c u v ∧ (u.point : ℝ) ≤ x ∧ x ≤ v.point := by
  exact PrimeFactorUnimodality.ThetaSquaredCheckpoint.Chain.covers h hpx hxq

example {c : ℚ} (hc : 0 ≤ c) {p q : ThetaSquaredCheckpoint}
    {rows : List ThetaSquaredCheckpoint} (h : Chain c p q rows)
    (hvalid : ∀ r ∈ rows, r.Valid) {x : ℝ}
    (hpx : (p.point : ℝ) ≤ x) (hxq : x ≤ q.point) :
    |Chebyshev.theta x - x| ≤ (c : ℝ) * x / Real.log x ^ 2 := by
  exact PrimeFactorUnimodality.ThetaSquaredCheckpoint.Chain.bound hc h hvalid hpx hxq

example {left right : List ThetaSquaredCheckpoint}
    (hl : ∀ p ∈ left, p.Valid) (hr : ∀ p ∈ right, p.Valid) :
    ∀ p ∈ left ++ right, p.Valid := by
  exact PrimeFactorUnimodality.ThetaSquaredCheckpoint.valid_append hl hr

private def p : ThetaSquaredCheckpoint := ⟨2, 0, 2, 2⟩
private def q : ThetaSquaredCheckpoint := ⟨3, 0, 3, 2⟩
private def r : ThetaSquaredCheckpoint := ⟨4, 0, 4, 2⟩

private theorem leftChain : Chain 6 p q [p, q] :=
  .cons p (by norm_num [Step, p, q]) (.single q (by norm_num [Step, q]))

private theorem rightChain : Chain 6 q r [q, r] :=
  .cons q (by norm_num [Step, q, r]) (.single r (by norm_num [Step, r]))

example : Chain 6 p r [p, q, q, r] := leftChain.append rightChain

example : ∃ u ∈ [p, q], ∃ v ∈ [p, q], Step 6 u v ∧
    (u.point : ℝ) ≤ (5 / 2 : ℝ) ∧ (5 / 2 : ℝ) ≤ v.point :=
  leftChain.covers (by norm_num [p]) (by norm_num [q])

example : ∃ u ∈ [p, q], ∃ v ∈ [p, q], Step 6 u v ∧
    (u.point : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ v.point :=
  leftChain.covers (by norm_num [p]) (by norm_num [q])

example : ∃ u ∈ [p, q], ∃ v ∈ [p, q], Step 6 u v ∧
    (u.point : ℝ) ≤ 3 ∧ (3 : ℝ) ≤ v.point :=
  leftChain.covers (by norm_num [p]) (by norm_num [q])

example (hvalid : ∀ s ∈ [p, q, q, r], s.Valid) :
    |Chebyshev.theta (5 / 2) - 5 / 2| ≤ (6 : ℝ) * (5 / 2) / Real.log (5 / 2) ^ 2 := by
  exact (leftChain.append rightChain).bound (by norm_num) hvalid
    (by norm_num [p]) (by norm_num [r])

end

end PrimeFactorUnimodality.Tests
