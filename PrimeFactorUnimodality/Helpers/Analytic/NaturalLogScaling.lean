import PrimeFactorUnimodality.Helpers.Analytic.RationalIntervalBounds
import PrimeFactorUnimodality.Helpers.Analytic.SharedTaylorIntervals

/-! # Checked logarithms of large natural numbers by binary scaling

Integer comparisons certify leading-bit bounds for a potentially very large
natural number. Only the small bounding significands enter Taylor evaluation;
the exponent scales a shared enclosure of log two. Logarithmic monotonicity
then certifies the supplied outward-rounded target interval.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core

/-- Positive bounding significands and their common binary exponent. -/
structure NatLogScaleRow where
  lower : ℕ
  upper : ℕ
  exponent : ℕ

namespace NatLogScaleRow

/-- Enclose both bounding logarithms using only significands and shared scalar constants. -/
def interval (row : NatLogScaleRow) (c : SharedTaylorIntervals) : IntervalRat :=
  IntervalRat.add (IntervalRat.hull (c.log row.lower) (c.log row.upper))
    (IntervalRat.scale row.exponent c.logTwo)

/-- Check the exact integer bounds and containment in the proposed logarithm interval. -/
def check (row : NatLogScaleRow) (c : SharedTaylorIntervals) (value : ℕ)
    (target : IntervalRat) : Bool :=
  decide (0 < row.lower ∧ row.lower ≤ row.upper ∧
    row.lower * 2 ^ row.exponent ≤ value ∧ value ≤ row.upper * 2 ^ row.exponent) &&
      intervalSubset (row.interval c) target

/-- Accepted scaling data encloses the logarithm of the actual natural number. -/
theorem log_mem_of_check (row : NatLogScaleRow) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {value : ℕ} {target : IntervalRat}
    (h : row.check c value target = true) : Real.log (value : ℝ) ∈ target := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hl, hlu, hlo, hhi⟩, hsubset⟩ := h
  have hlR : (0 : ℝ) < row.lower := by exact_mod_cast hl
  have huR : (0 : ℝ) < row.upper := by exact_mod_cast (hl.trans_le hlu)
  have hval : 0 < value := (Nat.mul_pos hl (Nat.two_pow_pos row.exponent)).trans_le hlo
  have hvR : (0 : ℝ) < value := by exact_mod_cast hval
  have hloR : (row.lower : ℝ) * (2 : ℝ) ^ row.exponent ≤ value := by exact_mod_cast hlo
  have hhiR : (value : ℝ) ≤ (row.upper : ℝ) * (2 : ℝ) ^ row.exponent := by exact_mod_cast hhi
  have hloglo := Real.log_le_log (mul_pos hlR (by positivity)) hloR
  have hloghi := Real.log_le_log hvR hhiR
  rw [Real.log_mul hlR.ne' (by positivity), Real.log_pow] at hloglo
  rw [Real.log_mul huR.ne' (by positivity), Real.log_pow] at hloghi
  have htwo : Real.log 2 ∈ c.logTwo := by rw [hc.logTwo]; exact IntervalRat.mem_ln2Computable _
  have hscale : (row.exponent : ℝ) * Real.log 2 ∈ IntervalRat.scale row.exponent c.logTwo := by
    simpa using IntervalRat.mem_scale (row.exponent : ℚ) htwo
  have hlow := SharedTaylorIntervals.mem_log hc (show (0 : ℚ) < row.lower by exact_mod_cast hl)
  have hhigh := SharedTaylorIntervals.mem_log hc
    (show (0 : ℚ) < row.upper by exact_mod_cast (hl.trans_le hlu))
  have hlow' : Real.log (row.lower : ℝ) + (row.exponent : ℝ) * Real.log 2 ∈ row.interval c := by
    simpa [interval] using
      IntervalRat.mem_add (IntervalRat.mem_hull_left (J := c.log row.upper) hlow) hscale
  have hhigh' : Real.log (row.upper : ℝ) + (row.exponent : ℝ) * Real.log 2 ∈ row.interval c := by
    simpa [interval] using
      IntervalRat.mem_add (IntervalRat.mem_hull_right (I := c.log row.lower) hhigh) hscale
  apply mem_of_intervalSubset hsubset
  change (row.interval c).lo ≤ Real.log (value : ℝ) ∧ Real.log (value : ℝ) ≤ (row.interval c).hi
  exact ⟨hlow'.1.trans hloglo, hloghi.trans hhigh'.2⟩

end NatLogScaleRow

end PrimeFactorUnimodality
