import PrimeFactorUnimodality.Helpers.Analytic.SharedXiGridCheck

/-! # Full grid-error interfaces and small rational boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open Fourier
open PrimeFactorUnimodality.SharedXiGridCheck

example {c : SharedXiGridCheck} (hc : c.Valid) (p : RationalGridPoint) :
    p.toGridPoint.height c.grid ∈ c.height p := by
  exact PrimeFactorUnimodality.SharedXiGridCheck.mem_height hc p

example (c : SharedXiGridCheck) (s : XiGridSignData)
    (h : c.phaseData.check c.scalar (c.height s.point) s.phase s.phaseError = false) :
    c.check s = false := by simp [SharedXiGridCheck.check, h]
example (c : SharedXiGridCheck) (s : XiGridSignData)
    (h : checkEulerRemainder c.endpoint (ZetaCorrectionIntervals.critical (c.height s.point))
      c.model.order c.bernoulliCap s.risingCap s.tailCap = false) :
    c.check s = false := by simp [SharedXiGridCheck.check, h]
example (c : SharedXiGridCheck) (s : XiGridSignData)
    (h : s.checkMargin c.rows c.model.degree c.scalar c.pi c.errors.cap = false) :
    c.check s = false := by simp [SharedXiGridCheck.check, h]

end

end PrimeFactorUnimodality.Tests
