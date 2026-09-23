import PrimeFactorUnimodality.Helpers.Analytic.CheckedZetaGrid
import PrimeFactorUnimodality.Helpers.Analytic.ZetaCorrectionIntervals

/-! # Executable short-correction checks at exact Fourier-grid heights

The grid coordinate uses its actual pi factor. Base height and window radius
are supplied by proved real enclosures, not assumed equal to floating-point
approximations. A successful sample check discharges both the window and
correction premises of the existing zeta and normalized-xi evaluator.
-/

namespace PrimeFactorUnimodality

open Complex LeanCert.Core

/-- Enclose the exact signed Fourier coordinate using one shared pi interval. -/
def zetaGridCoordinateInterval (P : IntervalRat) (levels : ℕ) (index : ℤ) : IntervalRat :=
  IntervalRat.scale (2 * (index : ℚ) / (2 : ℚ) ^ levels) P

/-- Negative and positive grid indices use the same proved coordinate formula. -/
theorem mem_zetaGridCoordinateInterval {P : IntervalRat} (hpi : Real.pi ∈ P)
    (levels : ℕ) (index : ℤ) :
    2 * Real.pi * index / (2 : ℝ) ^ levels ∈ zetaGridCoordinateInterval P levels index := by
  have h := IntervalRat.mem_scale (2 * (index : ℚ) / (2 : ℚ) ^ levels) hpi
  have he : 2 * Real.pi * index / (2 : ℝ) ^ levels =
      ((2 * (index : ℚ) / (2 : ℚ) ^ levels : ℚ) : ℝ) * Real.pi := by
    push_cast
    ring
  rw [he]
  exact h

/-- A rational check that includes every real member of the unit window. -/
def intervalWithinUnit (J : IntervalRat) : Bool := decide (-1 ≤ J.lo ∧ J.hi ≤ 1)

/-- The interval test bounds the absolute value of every enclosed coordinate. -/
theorem abs_le_one_of_intervalWithinUnit {J : IntervalRat} (h : intervalWithinUnit J = true)
    {x : ℝ} (hx : x ∈ J) : |x| ≤ 1 := by
  simp only [intervalWithinUnit, decide_eq_true_eq] at h
  apply abs_le.mpr
  constructor
  · exact le_trans (by exact_mod_cast h.1) hx.1
  · exact le_trans hx.2 (by exact_mod_cast h.2)

/-- Compact sample data retains just the grid index, phase period and rounded correction. -/
structure RationalGridPoint where
  index : ℤ
  turns : ℤ
  correction : RationalPoint
  error : ℚ

namespace RationalGridPoint

/-- Interpret the rational sample in the existing mathematical evaluator. -/
def toGridPoint (p : RationalGridPoint) : ZetaGridPoint :=
  ⟨p.index, p.correction.toComplex, p.error⟩

/-- Exact interval arithmetic supplies the non-rational grid height enclosure. -/
def heightInterval (p : RationalGridPoint) (levels : ℕ) (P B R : IntervalRat) : IntervalRat :=
  IntervalRat.add B (IntervalRat.mul R (zetaGridCoordinateInterval P levels p.index))

/-- No long Dirichlet prefix or Fourier transform is repeated by this sample check. -/
def check (p : RationalGridPoint) (levels : ℕ) (d : DirichletEndpointIntervals)
    (c : SharedTaylorIntervals) (P B R : IntervalRat) (coefficients : List ℚ) : Bool :=
  intervalWithinUnit (zetaGridCoordinateInterval P levels p.index) &&
    ZetaCorrectionIntervals.check d c P (p.heightInterval levels P B R)
      p.turns coefficients p.correction p.error

/-- Successful rational checks discharge both actual per-grid-point obligations. -/
theorem valid_of_check (p : RationalGridPoint) {g : ZetaGridBlock}
    {d : DirichletEndpointIntervals} (hd : d.Valid) (hN : d.cutoff = g.shared.cutoff)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {P B R : IntervalRat}
    (hpi : Real.pi ∈ P) (hbase : g.shared.base ∈ B) (hradius : g.shared.radius ∈ R)
    {coefficients : List ℚ} (hb : coefficients = eulerBernoulliCoefficients 1 g.shared.order)
    (h : p.check g.levels d c P B R coefficients = true) : p.toGridPoint.Valid g := by
  simp only [check, Bool.and_eq_true] at h
  have hcoord : p.toGridPoint.coordinate g ∈
      zetaGridCoordinateInterval P g.levels p.index :=
    mem_zetaGridCoordinateInterval hpi g.levels p.index
  have hheight : p.toGridPoint.height g ∈ p.heightInterval g.levels P B R :=
    IntervalRat.mem_add hbase (IntervalRat.mem_mul hradius hcoord)
  refine ⟨abs_le_one_of_intervalWithinUnit h.1 hcoord, ?_⟩
  have hcorr := ZetaCorrectionIntervals.norm_sub_le_of_check hd hc hpi hheight
    p.turns hb h.2
  rw [hN] at hcorr
  exact hcorr

/-- The checked sample feeds the actual zeta error theorem with the full Euler remainder. -/
theorem norm_zeta_sub_value_le (p : RationalGridPoint) {g : ZetaGridBlock} (hg : g.Valid)
    {d : DirichletEndpointIntervals} (hd : d.Valid) (hN : d.cutoff = g.shared.cutoff)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {P B R : IntervalRat}
    (hpi : Real.pi ∈ P) (hbase : g.shared.base ∈ B) (hradius : g.shared.radius ∈ R)
    {coefficients : List ℚ} (hb : coefficients = eulerBernoulliCoefficients 1 g.shared.order)
    (h : p.check g.levels d c P B R coefficients = true) :
    ‖riemannZeta ((1 / 2 : ℂ) + p.toGridPoint.height g * I) - p.toGridPoint.value g‖ ≤
      p.toGridPoint.error g :=
  (p.valid_of_check hd hN hc hpi hbase hradius hb h).norm_zeta_sub_value_le hg

end RationalGridPoint

end PrimeFactorUnimodality
