import PrimeFactorUnimodality.Helpers.Analytic.RationalIntervalBounds
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.RationalPoint

/-! # Complex rectangles with rational endpoint arithmetic

The two real intervals enclose rectangular complex sets. Multiplication,
addition, rational scaling and Euclidean error tests reuse their existing
real interval proofs; no floating-point value enters the semantics.
-/

namespace PrimeFactorUnimodality

open Complex LeanCert.Core

/-- A complex rectangle with rational endpoints. -/
structure ComplexInterval where
  re : IntervalRat
  im : IntervalRat
  deriving DecidableEq, Repr

namespace ComplexInterval

instance : Membership ℂ ComplexInterval where
  mem J z := z.re ∈ J.re ∧ z.im ∈ J.im

/-- An exact Gaussian rational point. -/
def point (q : RationalPoint) : ComplexInterval :=
  ⟨IntervalRat.singleton q.re, IntervalRat.singleton q.im⟩

/-- An interval on the real axis. -/
def real (J : IntervalRat) : ComplexInterval := ⟨J, IntervalRat.singleton 0⟩

/-- An interval on the imaginary axis. -/
def imag (J : IntervalRat) : ComplexInterval := ⟨IntervalRat.singleton 0, J⟩

/-- Componentwise rectangular addition. -/
def add (J K : ComplexInterval) : ComplexInterval :=
  ⟨IntervalRat.add J.re K.re, IntervalRat.add J.im K.im⟩

/-- Rectangular multiplication includes the full cross-term dependence. -/
def mul (J K : ComplexInterval) : ComplexInterval :=
  ⟨IntervalRat.sub (IntervalRat.mul J.re K.re) (IntervalRat.mul J.im K.im),
    IntervalRat.add (IntervalRat.mul J.re K.im) (IntervalRat.mul J.im K.re)⟩

/-- Rational scaling handles either sign of the scalar. -/
def scale (q : ℚ) (J : ComplexInterval) : ComplexInterval :=
  ⟨IntervalRat.mul (IntervalRat.singleton q) J.re,
    IntervalRat.mul (IntervalRat.singleton q) J.im⟩

/-- Exact rational points belong to their degenerate rectangles. -/
theorem mem_point (q : RationalPoint) : q.toComplex ∈ point q :=
  ⟨IntervalRat.mem_singleton q.re, IntervalRat.mem_singleton q.im⟩

/-- Rational constants are enclosed on the real axis. -/
theorem mem_constant (q : ℚ) : (q : ℂ) ∈ point ⟨q, 0⟩ := by
  constructor <;> simp [point, IntervalRat.mem_def, IntervalRat.singleton]

/-- Inclusion of a real-axis value. -/
theorem mem_real {x : ℝ} {J : IntervalRat} (hx : x ∈ J) : (x : ℂ) ∈ real J :=
  ⟨hx, by simpa [real] using IntervalRat.mem_singleton 0⟩

/-- Inclusion of an imaginary-axis value. -/
theorem mem_imag {x : ℝ} {J : IntervalRat} (hx : x ∈ J) : I * (x : ℂ) ∈ imag J := by
  change (I * (x : ℂ)).re ∈ IntervalRat.singleton 0 ∧ (I * (x : ℂ)).im ∈ J
  simpa using And.intro (IntervalRat.mem_singleton 0) hx

/-- Addition preserves every enclosed pair of values. -/
theorem mem_add {z w : ℂ} {J K : ComplexInterval} (hz : z ∈ J) (hw : w ∈ K) :
    z + w ∈ add J K :=
  ⟨IntervalRat.mem_add hz.1 hw.1, IntervalRat.mem_add hz.2 hw.2⟩

/-- Multiplication preserves every enclosed pair of values. -/
theorem mem_mul {z w : ℂ} {J K : ComplexInterval} (hz : z ∈ J) (hw : w ∈ K) :
    z * w ∈ mul J K :=
  ⟨IntervalRat.mem_sub (IntervalRat.mem_mul hz.1 hw.1) (IntervalRat.mem_mul hz.2 hw.2),
    IntervalRat.mem_add (IntervalRat.mem_mul hz.1 hw.2) (IntervalRat.mem_mul hz.2 hw.1)⟩

/-- Rational scaling needs no nonnegativity hypothesis. -/
theorem mem_scale (q : ℚ) {z : ℂ} {J : ComplexInterval} (hz : z ∈ J) :
    (q : ℂ) * z ∈ scale q J := by
  change ((q : ℂ) * z).re ∈ _ ∧ ((q : ℂ) * z).im ∈ _
  simpa [scale] using And.intro
    (IntervalRat.mem_mul (IntervalRat.mem_singleton q) hz.1)
    (IntervalRat.mem_mul (IntervalRat.mem_singleton q) hz.2)

/-- A full rectangular containment test, useful for rounded checkpoints. -/
def subset (J K : ComplexInterval) : Bool :=
  intervalSubset J.re K.re && intervalSubset J.im K.im

/-- Containment allows outward rounding without losing the exact value. -/
theorem mem_of_subset {J K : ComplexInterval} (h : subset J K = true)
    {z : ℂ} (hz : z ∈ J) : z ∈ K := by
  simp only [subset, Bool.and_eq_true] at h
  exact ⟨mem_of_intervalSubset h.1 hz.1, mem_of_intervalSubset h.2 hz.2⟩

/-- Squared Euclidean error test for every point of a rectangle. -/
def close (J : ComplexInterval) (q : RationalPoint) (e : ℚ) : Bool :=
  decide (0 ≤ e ∧ (intervalPointRadius J.re q.re) ^ 2 +
    (intervalPointRadius J.im q.im) ^ 2 ≤ e ^ 2)

/-- A successful rational test bounds the exact complex error. -/
theorem norm_sub_le_of_close {J : ComplexInterval} {q : RationalPoint} {e : ℚ}
    (h : close J q e = true) {z : ℂ} (hz : z ∈ J) :
    ‖z - q.toComplex‖ ≤ (e : ℝ) := by
  simp only [close, decide_eq_true_eq] at h
  apply q.norm_sub_le_of_component_bounds
    (abs_sub_le_intervalPointRadius hz.1 q.re)
    (abs_sub_le_intervalPointRadius hz.2 q.im)
  · exact_mod_cast h.1
  · exact_mod_cast h.2

/-- A zero-centered error test also certifies a norm cap without taking square roots. -/
theorem norm_le_of_close_zero {J : ComplexInterval} {e : ℚ}
    (h : close J ⟨0, 0⟩ e = true) {z : ℂ} (hz : z ∈ J) : ‖z‖ ≤ (e : ℝ) := by
  have hb := norm_sub_le_of_close h hz
  have hzero : (⟨0, 0⟩ : RationalPoint).toComplex = 0 := by
    apply Complex.ext <;> simp [RationalPoint.toComplex]
  simpa only [hzero, sub_zero] using hb

end ComplexInterval

end PrimeFactorUnimodality
