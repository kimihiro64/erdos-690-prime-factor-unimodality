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

example (c : SharedXiGridCheck) (s : XiGridSignData)
    (h : c.phaseData.check c.scalar (c.height s.point) s.phase s.phaseError = false) :
    c.checkSign s = false := by simp [SharedXiGridCheck.checkSign, h]
example (c : SharedXiGridCheck) (s : XiGridSignData)
    (h : checkEulerRemainder c.endpoint (ZetaCorrectionIntervals.critical (c.height s.point))
      c.model.order c.bernoulliCap s.risingCap s.tailCap = false) :
    c.checkSign s = false := by simp [SharedXiGridCheck.checkSign, h]
example (c : SharedXiGridCheck) (s : XiGridSignData)
    (hp : s.point.check c.rows.levels c.endpoint c.scalar c.pi c.base c.radius c.coefficients = true)
    (hθ : c.phaseData.check c.scalar (c.height s.point) s.phase s.phaseError = true)
    (he : checkEulerRemainder c.endpoint (ZetaCorrectionIntervals.critical (c.height s.point))
      c.model.order c.bernoulliCap s.risingCap s.tailCap = true)
    (hm : s.checkCardinalMargin c.rows c.model.degree c.pi c.errors.cap = true) :
    c.checkSign s = true := by simp [SharedXiGridCheck.checkSign, hp, hθ, he, hm]
example (c : SharedXiGridCheck) (s : XiGridSignData)
    (hp : s.point.check c.rows.levels c.endpoint c.scalar c.pi c.base c.radius c.coefficients = true)
    (hθ : c.phaseData.check c.scalar (c.height s.point) s.phase s.phaseError = true)
    (he : checkEulerRemainder c.endpoint (ZetaCorrectionIntervals.critical (c.height s.point))
      c.model.order c.bernoulliCap s.risingCap s.tailCap = true)
    (hm : s.checkProjectionMargin c.rows c.model.degree c.scalar c.pi c.errors.cap = true) :
    c.checkSign s = true := by
  simp [SharedXiGridCheck.checkSign, XiGridSignData.checkSignMargin, hp, hθ, he, hm]

end

end PrimeFactorUnimodality.Tests
