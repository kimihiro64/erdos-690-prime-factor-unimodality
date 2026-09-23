import PrimeFactorUnimodality.Helpers.Analytic.EulerRemainderIntervals
import PrimeFactorUnimodality.Helpers.Analytic.RationalGridErrorBudget

/-! # The complete actual grid error has a checked rational cap

Combine the once-per-block moment, transform and Taylor budget with the
per-height scaled Euler remainder and the retained correction error. This
discharges the full error premise used by the numerical xi sign comparison.
-/

namespace PrimeFactorUnimodality.RationalGridPoint

open Complex LeanCert.Core Polynomial

/-- All components of the original grid error are bounded by checked rational data. -/
theorem error_le_of_checks (p : RationalGridPoint) (r : RationalGridRows)
    (d : ZetaGroupedBlock) (hg : (r.attach d).Valid)
    (b : RationalGridErrorBudget) (hm : ∀ k j, d.coefficientError k j = (b.moment k j : ℝ))
    {expHalf : IntervalRat} (he : Real.exp (1 / 2) ∈ expHalf)
    (hb : b.check r d.cutoff d.degree expHalf = true)
    {endpoint : DirichletEndpointIntervals} (hd : endpoint.Valid) (hN : endpoint.cutoff = d.cutoff)
    {P B R : IntervalRat} (hpi : Real.pi ∈ P) (hbase : d.base ∈ B) (hradius : d.radius ∈ R)
    (hw : intervalWithinUnit (zetaGridCoordinateInterval P r.levels p.index) = true)
    {C M E : ℚ} (hC : C = bernoulliCoeffBudget (d.order + 1))
    (hE : checkEulerRemainder endpoint
      (ZetaCorrectionIntervals.critical (p.heightInterval r.levels P B R)) d.order C M E = true) :
    p.toGridPoint.error (r.attach d) ≤ ((E + b.cap + p.error : ℚ) : ℝ) := by
  have hcoord := mem_zetaGridCoordinateInterval hpi r.levels p.index
  have hheight : p.toGridPoint.height (r.attach d) ∈ p.heightInterval r.levels P B R :=
    IntervalRat.mem_add hbase (IntervalRat.mem_mul hradius hcoord)
  have htail := zetaEulerError_le_of_check hd (ZetaCorrectionIntervals.mem_critical hheight)
    (by norm_num) d.order hC hE
  rw [hN] at htail
  have hshared := b.error_le_of_check r d hg hm he hb p
    (abs_le_one_of_intervalWithinUnit hw hcoord)
  push_cast
  exact hshared.trans (add_le_add (add_le_add htail le_rfl) le_rfl)

end PrimeFactorUnimodality.RationalGridPoint
