import PrimeFactorUnimodality.Helpers.Analytic.CheckedXiGridSigns

/-! # Full grid-error interfaces and small rational boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open Fourier
open PrimeFactorUnimodality

example {c : SharedXiGridCheck} (hc : c.Valid) (s : XiGridSignData)
    (h : c.check s = true) :
    s.point.toGridPoint.Valid c.grid ∧
    |turingStirlingPhase (s.point.toGridPoint.height c.grid) - (s.phase : ℝ)| ≤
      (s.phaseError : ℝ) ∧
    (if s.positive then
      s.point.toGridPoint.xiError c.grid s.phaseError < s.point.toGridPoint.xiApprox c.grid s.phase
    else s.point.toGridPoint.xiApprox c.grid s.phase < -s.point.toGridPoint.xiError c.grid s.phaseError) := by
  exact PrimeFactorUnimodality.SharedXiGridCheck.validated hc s h

example {c : SharedXiGridCheck} (hc : c.Valid) (s : XiGridSignData)
    (h : c.check s = true) :
    if s.positive then 0 < xiCriticalLineValue (s.point.toGridPoint.height c.grid)
    else xiCriticalLineValue (s.point.toGridPoint.height c.grid) < 0 := by
  exact PrimeFactorUnimodality.SharedXiGridCheck.sign_of_check hc s h

example {c : SharedXiGridCheck} (hc : c.Valid)
    (base span : ℚ) (hs : 0 < span) (hb : c.model.base = (base : ℝ))
    (hr : c.model.radius = rationalGridRadius span) (p q : XiGridSignData)
    (hp : c.check p = true) (hq : c.check q = true)
    (hij : p.point.index < q.point.index) (hopposite : p.positive ≠ q.positive) :
    (rationalGridSignRow base span c.rows.levels p.point.index q.point.index).Valid := by
  exact PrimeFactorUnimodality.XiSignRow.valid_of_checked_grid hc base span hs hb hr p q hp hq hij hopposite



end

end PrimeFactorUnimodality.Tests
