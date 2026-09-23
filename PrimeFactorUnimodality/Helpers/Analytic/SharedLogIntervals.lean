import PrimeFactorUnimodality.Helpers.Analytic.SharedTaylorIntervals

/-! # Prepared logarithm enclosures on positive real intervals

Only the two rational endpoints are evaluated. Logarithmic monotonicity
covers every real point between them, including non-rational grid heights.
-/

namespace PrimeFactorUnimodality.SharedTaylorIntervals

open LeanCert.Core

/-- Prepared endpoint logarithms enclose a whole positive interval. -/
def logInterval (c : SharedTaylorIntervals) (J : IntervalRat) : IntervalRat :=
  IntervalRat.hull (c.log J.lo) (c.log J.hi)

/-- Monotonicity fills the real interval between the two checked endpoints. -/
theorem mem_logInterval {c : SharedTaylorIntervals} (hc : c.Prepared)
    {J : IntervalRat} (hJ : 0 < J.lo) {x : ℝ} (hx : x ∈ J) :
    Real.log x ∈ c.logInterval J := by
  have hl := mem_log hc hJ
  have hu := mem_log hc (lt_of_lt_of_le hJ J.le)
  have hpos : (0 : ℝ) < J.lo := Rat.cast_pos.mpr hJ
  have hxpos : 0 < x := hpos.trans_le hx.1
  simp only [logInterval, IntervalRat.mem_def, IntervalRat.hull, Rat.cast_min, Rat.cast_max]
  constructor
  · exact (min_le_left _ _).trans (hl.1.trans (Real.log_le_log hpos hx.1))
  · exact ((Real.log_le_log hxpos hx.2).trans hu.2).trans (le_max_right _ _)

end PrimeFactorUnimodality.SharedTaylorIntervals
