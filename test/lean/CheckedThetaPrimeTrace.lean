import PrimeFactorUnimodality.Helpers.Analytic.CheckedThetaPrimeTrace

/-! # Complete prime-block transitions and coverage regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open LeanCert.Core
open PrimeFactorUnimodality.ThetaPrimeCheckpoint

example {c : SharedTaylorIntervals} (hc : c.Prepared)
    {s : ThetaPrimeCheckpoint} (h : checkLog c s = true) : Real.log s.point ∈ s.log := by
  exact PrimeFactorUnimodality.ThetaPrimeCheckpoint.log_mem_of_check hc h

example {c : SharedTaylorIntervals} (hc : c.Prepared)
    {start : ThetaPrimeCheckpoint} (hs : start.Valid) {points : List ThetaPrimeCheckpoint}
    (hcounts : ∀ s ∈ points, Nat.primeCounting s.point = s.count)
    (h : checkTrace c start points = true) : ∀ s ∈ points, s.Valid := by
  exact PrimeFactorUnimodality.ThetaPrimeCheckpoint.valid_of_checkTrace hc hs hcounts h

example (c : SharedTaylorIntervals) (start : ThetaPrimeCheckpoint)
    (left right : List ThetaPrimeCheckpoint) :
    checkTrace c start (left ++ right) =
      (checkTrace c start left && checkTrace c (left.getLast?.getD start) right) := by
  exact PrimeFactorUnimodality.ThetaPrimeCheckpoint.checkTrace_append c start left right

example {c : SharedTaylorIntervals} (hc : c.Prepared)
    {start : ThetaPrimeCheckpoint} (hs : start.Valid) {points : List ThetaPrimeCheckpoint}
    (hcounts : ∀ s ∈ points, Nat.primeCounting s.point = s.count)
    (h : checkTrace c start points = true)
    (hpoint : ∀ s ∈ points, 2 ≤ s.point ∧ 0 < s.log.hi) :
    ∀ p ∈ points.map squared, p.Valid := by
  exact PrimeFactorUnimodality.ThetaPrimeCheckpoint.squared_valid_of_checkTrace hc hs hcounts h hpoint

private def two : ThetaPrimeCheckpoint :=
  ⟨2, 1, ⟨0, 1, by norm_num⟩, ⟨0, 1, by norm_num⟩⟩

private def three : ThetaPrimeCheckpoint :=
  ⟨3, 2, ⟨0, 3, by norm_num⟩, ⟨1, 2, by norm_num⟩⟩

example : checkTrace (SharedTaylorIntervals.prepare 4) one [two, three] = true := by
  decide +kernel

example : checkLog (SharedTaylorIntervals.prepare 4)
    ⟨0, 0, IntervalRat.singleton 0, IntervalRat.singleton 0⟩ = false := by decide +kernel

example : checkTrace (SharedTaylorIntervals.prepare 4) three [] = true := rfl

example : three.Valid := by
  have hcounts : ∀ s ∈ [two, three], Nat.primeCounting s.point = s.count := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · have hp : Nat.primesLE 2 = {2} := by decide +kernel
      change Nat.primeCounting 2 = 1
      rw [← Nat.primesLE_card_eq_primeCounting, hp]
      simp
    · have hp : Nat.primesLE 3 = {2, 3} := by decide +kernel
      change Nat.primeCounting 3 = 2
      rw [← Nat.primesLE_card_eq_primeCounting, hp]
      norm_num
  exact valid_of_checkTrace (SharedTaylorIntervals.prepare_prepared 4) one_valid hcounts
    (by decide +kernel) three (by simp)

end

end PrimeFactorUnimodality.Tests
