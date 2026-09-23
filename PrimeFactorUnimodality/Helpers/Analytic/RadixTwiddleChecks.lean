import LeanCert.Core.IntervalRat.Taylor
import PrimeFactorUnimodality.Helpers.Analytic.RationalIntervalBounds
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RationalTrace

/-! # Computable shared twiddle checks from proved sine and cosine intervals

The exact angles lie in one bounded period. Use direct Taylor enclosures
and Mathlib's twenty-digit pi interval; no coarse large-angle reduction
or unverified external phase value is used.
-/

namespace PrimeFactorUnimodality

open Complex Fourier LeanCert.Core
open LeanCert.Core.IntervalRat

/-- A proved narrow pi interval, independent of any supplied phase data. -/
def twiddlePi : IntervalRat :=
  ⟨3.14159265358979323846, 3.14159265358979323847, by norm_num⟩

/-- Mathlib's proved decimal bounds enclose the actual pi. -/
theorem pi_mem_twiddlePi : Real.pi ∈ twiddlePi := by
  constructor
  · exact_mod_cast Real.pi_gt_d20.le
  · exact_mod_cast Real.pi_lt_d20.le

/-- Rational interval for one canonical Fourier angle. -/
def twiddleAngle (n k : ℕ) : IntervalRat :=
  mul (singleton ((2 * k : ℚ) / (2 ^ n))) twiddlePi

/-- The interval contains the exact angle, including the zero index. -/
theorem angle_mem_twiddleAngle (n k : ℕ) :
    2 * Real.pi * k / (2 ^ n) ∈ twiddleAngle n k := by
  have h := mem_mul (mem_singleton ((2 * k : ℚ) / (2 ^ n))) pi_mem_twiddlePi
  have he : (((2 * k : ℚ) / (2 ^ n) : ℚ) : ℝ) * Real.pi =
      2 * Real.pi * k / (2 ^ n) := by push_cast; ring
  rw [he] at h
  exact h

/-- Only rational comparisons remain after the proved trigonometric enclosures. -/
def checkTwiddle (n k order : ℕ) (q : RationalPoint) (e : ℚ) : Bool :=
  let angle := twiddleAngle n k
  let x := intervalPointRadius (cosComputable angle order) q.re
  let y := intervalPointRadius (sinComputable angle order) q.im
  decide (0 ≤ e ∧ x ^ 2 + y ^ 2 ≤ e ^ 2)

/-- A successful rational check bounds the actual canonical twiddle. -/
theorem checkTwiddle_sound (n k order : ℕ) (q : RationalPoint) (e : ℚ)
    (h : checkTwiddle n k order q e = true) :
    ‖radixRoot n ^ k - q.toComplex‖ ≤ (e : ℝ) := by
  simp only [checkTwiddle, decide_eq_true_eq] at h
  have hx := abs_sub_le_intervalPointRadius
    (mem_cosComputable (angle_mem_twiddleAngle n k) order) q.re
  have hy := abs_sub_le_intervalPointRadius
    (mem_sinComputable (angle_mem_twiddleAngle n k) order) q.im
  rw [radixRoot_pow]
  apply q.norm_sub_le_of_component_bounds
    (x := (intervalPointRadius (cosComputable (twiddleAngle n k) order) q.re : ℝ))
    (y := (intervalPointRadius (sinComputable (twiddleAngle n k) order) q.im : ℝ))
  · simpa only [Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_add,
      Real.exp_zero] using hx
  · simpa only [Complex.exp_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_add,
      Real.exp_zero] using hy
  · exact_mod_cast h.1
  · exact_mod_cast h.2

/-- Every depth table is checked once, independently of the number of transform columns. -/
def checkTwiddleTables (p : RationalTwiddles) (depth order : ℕ) : Bool :=
  allIndices fun n : Fin depth => decide (0 ≤ p.error n.val) &&
    allIndices fun k : Fin (2 ^ (n.val + 1)) =>
      checkTwiddle (n.val + 1) k.val order (p.table n.val)[k.val] (p.error n.val)

/-- The shared table checker supplies all analytic phase hypotheses of the rational assembler. -/
theorem checkTwiddleTables_sound (p : RationalTwiddles) (depth order : ℕ)
    (h : checkTwiddleTables p depth order = true) : p.Valid depth := by
  intro n hn
  have hrow := (allIndices_eq_true _).mp h ⟨n, hn⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, allIndices_eq_true] at hrow
  refine ⟨by exact_mod_cast hrow.1, ?_⟩
  intro k
  exact checkTwiddle_sound _ _ _ _ _ (hrow.2 k)

end PrimeFactorUnimodality
