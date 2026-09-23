import LeanCert.Core.IntervalRat.Taylor
import PrimeFactorUnimodality.Helpers.Analytic.RationalIntervalBounds
import PrimeFactorUnimodality.Helpers.Analytic.ThetaSquaredCheckpoints
import PrimeFactorUnimodality.Mathlib.NumberTheory.Chebyshev.Intervals

/-! # Shared theta checkpoints from interval prime counts

Each retained endpoint stores its prime count, theta enclosure and logarithm
once. A transition bounds all newly added prime logarithms by the two endpoint
logs. Rational containment permits rounding the accumulated interval outward
at every checkpoint. Prime counts and logarithms must still be certified.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core

/-- Retained exact count and rational enclosures at one integer endpoint. -/
structure ThetaPrimeCheckpoint where
  point : ℕ
  count : ℕ
  theta : IntervalRat
  log : IntervalRat

namespace ThetaPrimeCheckpoint

/-- The retained count and both enclosures refer to the actual analytic quantities. -/
def Valid (s : ThetaPrimeCheckpoint) : Prop :=
  0 < s.point ∧ Nat.primeCounting s.point = s.count ∧
    Chebyshev.theta s.point ∈ s.theta ∧ Real.log s.point ∈ s.log

/-- Bound the added prime weights with only shared endpoint logarithms. -/
def increment (s t : ThetaPrimeCheckpoint) : IntervalRat :=
  IntervalRat.scale (t.count - s.count : ℕ) (IntervalRat.hull s.log t.log)

/-- Ordered exact counts and endpoint logs enclose the complete theta increment. -/
theorem mem_increment {s t : ThetaPrimeCheckpoint} (hs : s.Valid)
    (hst : s.point ≤ t.point) (hcount : Nat.primeCounting t.point = t.count)
    (hlog : Real.log t.point ∈ t.log) :
    Chebyshev.theta t.point - Chebyshev.theta s.point ∈ s.increment t := by
  have hlo := Chebyshev.primeCounting_sub_mul_log_le_theta_sub hs.1 hst
  have hhi := Chebyshev.theta_sub_le_primeCounting_sub_mul_log hst
  rw [hs.2.1, hcount] at hlo hhi
  have hnonneg : (0 : ℝ) ≤ (t.count - s.count : ℕ) := by positivity
  have hl : (min s.log.lo t.log.lo : ℝ) ≤ Real.log s.point :=
    (min_le_left _ _).trans hs.2.2.2.1
  have hu : Real.log t.point ≤ (max s.log.hi t.log.hi : ℝ) :=
    hlog.2.trans (le_max_right _ _)
  simp only [increment, IntervalRat.scale, IntervalRat.hull, IntervalRat.mem_def]
  split_ifs with h
  · push_cast
    exact ⟨(mul_le_mul_of_nonneg_left hl hnonneg).trans hlo,
      hhi.trans (mul_le_mul_of_nonneg_left hu hnonneg)⟩
  · exact False.elim (h (Nat.cast_nonneg _))

/-- A local rational check permits outward rounding without recomputing old prime weights. -/
def checkStep (s t : ThetaPrimeCheckpoint) : Bool :=
  decide (s.point ≤ t.point ∧ s.count ≤ t.count) &&
    intervalSubset (IntervalRat.add s.theta (s.increment t)) t.theta

/-- Exact new count and log data plus a checked transition validate the new theta endpoint. -/
theorem valid_of_checkStep {s t : ThetaPrimeCheckpoint} (hs : s.Valid)
    (hcount : Nat.primeCounting t.point = t.count) (hlog : Real.log t.point ∈ t.log)
    (h : s.checkStep t = true) : t.Valid := by
  simp only [checkStep, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨hs.1.trans_le h.1.1, hcount, ?_, hlog⟩
  have ht := mem_of_intervalSubset h.2
    (IntervalRat.mem_add hs.2.2.1 (mem_increment hs h.1.1 hcount hlog))
  simpa using ht

/-- The origin for positive integer checkpoints has exact empty prime count and theta sum. -/
def one : ThetaPrimeCheckpoint :=
  ⟨1, 0, IntervalRat.singleton 0, IntervalRat.singleton 0⟩

/-- The initial checkpoint has no numerical certificate obligation. -/
theorem one_valid : one.Valid := by
  norm_num [one, Valid, IntervalRat.mem_def, IntervalRat.singleton, Chebyshev.theta_one]

/-- Export the existing lower-band row interface without changing any stored endpoint. -/
def squared (s : ThetaPrimeCheckpoint) : ThetaSquaredCheckpoint :=
  ⟨s.point, s.theta.lo, s.theta.hi, s.log.hi⟩

/-- A valid retained state supplies all three real bounds of a squared-error checkpoint. -/
theorem squared_valid {s : ThetaPrimeCheckpoint} (hs : s.Valid) (hpoint : 2 ≤ s.point)
    (hlog : 0 < s.log.hi) : s.squared.Valid :=
  ⟨hpoint, hlog, hs.2.2.1.1, hs.2.2.1.2, hs.2.2.2.2⟩

end ThetaPrimeCheckpoint

end PrimeFactorUnimodality
