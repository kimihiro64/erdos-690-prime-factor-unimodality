import PrimeFactorUnimodality.Helpers.Analytic.CheckedZetaGridPoints
import PrimeFactorUnimodality.Helpers.Analytic.XiSimplePhaseIntervals

/-! # Checked short corrections and elementary phases bound actual xi

The exact grid height is enclosed once and reused by the correction and
phase checks. Their successful rational computations discharge both
numerical premises of the existing normalized-xi error theorem.
-/

namespace PrimeFactorUnimodality.RationalGridPoint

open LeanCert.Core

/-- Actual normalized xi is bounded by the checked correction and phase errors. -/
theorem abs_xi_sub_approx_le_of_checks (p : RationalGridPoint) {g : ZetaGridBlock}
    (hg : g.Valid) {d : DirichletEndpointIntervals} (hd : d.Valid)
    (hN : d.cutoff = g.shared.cutoff) {c : SharedTaylorIntervals} (hc : c.Prepared)
    {P B R : IntervalRat} (hpi : Real.pi ∈ P) (hbase : g.shared.base ∈ B)
    (hradius : g.shared.radius ∈ R) {coefficients : List ℚ}
    (hb : coefficients = eulerBernoulliCoefficients 1 g.shared.order)
    (h : p.check g.levels d c P B R coefficients = true)
    {phaseData : XiSimplePhaseIntervals} (hp : phaseData.Valid) {phase error : ℚ}
    (hphase : phaseData.check c (p.heightInterval g.levels P B R) phase error = true) :
    |xiNormalizedValue (p.toGridPoint.height g) - p.toGridPoint.xiApprox g phase| ≤
      p.toGridPoint.xiError g error := by
  have hpoint := p.valid_of_check hd hN hc hpi hbase hradius hb h
  have hheight : p.toGridPoint.height g ∈ p.heightInterval g.levels P B R :=
    IntervalRat.mem_add hbase (IntervalRat.mem_mul hradius
      (mem_zetaGridCoordinateInterval hpi g.levels p.index))
  exact hpoint.abs_xi_sub_approx_le hg
    (XiSimplePhaseIntervals.abs_stirling_sub_le_of_check hp hc hheight hphase)

end PrimeFactorUnimodality.RationalGridPoint
