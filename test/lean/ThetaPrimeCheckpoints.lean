import PrimeFactorUnimodality.Helpers.Analytic.ThetaPrimeCheckpoints

/-! # Complete prime-block transitions and coverage regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open LeanCert.Core
open PrimeFactorUnimodality.ThetaPrimeCheckpoint

example {s t : ThetaPrimeCheckpoint} (hs : s.Valid)
    (hst : s.point ≤ t.point) (hcount : Nat.primeCounting t.point = t.count)
    (hlog : Real.log t.point ∈ t.log) :
    Chebyshev.theta t.point - Chebyshev.theta s.point ∈ s.increment t := by
  exact PrimeFactorUnimodality.ThetaPrimeCheckpoint.mem_increment hs hst hcount hlog

example {s t : ThetaPrimeCheckpoint} (hs : s.Valid)
    (hcount : Nat.primeCounting t.point = t.count) (hlog : Real.log t.point ∈ t.log)
    (h : s.checkStep t = true) : t.Valid := by
  exact PrimeFactorUnimodality.ThetaPrimeCheckpoint.valid_of_checkStep hs hcount hlog h

example : one.Valid := by
  exact PrimeFactorUnimodality.ThetaPrimeCheckpoint.one_valid

example {s : ThetaPrimeCheckpoint} (hs : s.Valid) (hpoint : 2 ≤ s.point)
    (hlog : 0 < s.log.hi) : s.squared.Valid := by
  exact PrimeFactorUnimodality.ThetaPrimeCheckpoint.squared_valid hs hpoint hlog

example : one.checkStep one = true := by decide +kernel

example : one.checkStep ⟨0, 0, IntervalRat.singleton 0, IntervalRat.singleton 0⟩ = false := by
  decide +kernel

example : (one.increment one).lo = 0 ∧ (one.increment one).hi = 0 := by decide +kernel

end

end PrimeFactorUnimodality.Tests
