import PrimeFactorUnimodality.Helpers.Analytic.ComplexInterval
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.RotationError

/-! # Exact signed-component projections at integer quarter turns

No sine or cosine interval is needed: multiplication by a power of `I`
selects a signed real or imaginary component. The integer is unrestricted;
negative turns and complete periods use the same four branches.
-/

namespace PrimeFactorUnimodality.ComplexInterval

open Complex LeanCert.Core

/-- Real projection after an integer number of quarter turns, using only endpoint negation. -/
def quarterRe (q : ℤ) (J : ComplexInterval) : IntervalRat :=
  if q % 4 = 0 then J.re else if q % 4 = 1 then IntervalRat.neg J.im
  else if q % 4 = 2 then IntervalRat.neg J.re else J.im

/-- Exact quarter-turn reduction validates all four signed-component branches. -/
theorem mem_quarterRe (q : ℤ) {z : ℂ} {J : ComplexInterval} (hz : z ∈ J) :
    (exp (I * (((q : ℝ) * Real.pi / 2 : ℝ) : ℂ)) * z).re ∈ quarterRe q J := by
  rw [exp_int_quarter_turn]
  have hlo := Int.emod_nonneg q (by norm_num : (4 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos q (by norm_num : (0 : ℤ) < 4)
  interval_cases hq : q % 4
  · simpa [quarterRe, hq] using hz.1
  · simpa [quarterRe, hq] using IntervalRat.mem_neg hz.2
  · simpa [quarterRe, hq, I_sq] using IntervalRat.mem_neg hz.1
  · simpa [quarterRe, hq, I_pow_three] using hz.2

end PrimeFactorUnimodality.ComplexInterval
