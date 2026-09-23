import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import PrimeFactorUnimodality.Helpers.Analytic.ComplexInterval
import PrimeFactorUnimodality.Helpers.Analytic.SharedTaylorIntervals

/-! # Rigorous shared Dirichlet atoms with integer phase reduction

A logarithm enclosure serves both the amplitude and the residual frequency.
An arbitrary integer number of periods is subtracted using a supplied proved
pi enclosure. Correctness does not assume that the integer is a rounded
transcendental value; choosing a good integer only controls interval width.
-/

namespace PrimeFactorUnimodality

open Complex LeanCert.Core

/-- Reduce the large base-height phase using rational arithmetic and an explicit pi interval. -/
def dirichletReducedPhase (L P : IntervalRat) (base : ℚ) (turns : ℤ) : IntervalRat :=
  IntervalRat.sub (IntervalRat.scale (-base) L) (IntervalRat.scale (2 * turns) P)

/-- The exact shifted phase is retained for every integer period choice. -/
theorem mem_dirichletReducedPhase {L P : IntervalRat} {x : ℝ}
    (hx : x ∈ L) (hpi : Real.pi ∈ P) (base : ℚ) (turns : ℤ) :
    -(base : ℝ) * x - (turns : ℝ) * (2 * Real.pi) ∈
      dirichletReducedPhase L P base turns := by
  have h := IntervalRat.mem_sub (IntervalRat.mem_scale (-base) hx)
    (IntervalRat.mem_scale (2 * turns) hpi)
  have he : -(base : ℝ) * x - (turns : ℝ) * (2 * Real.pi) =
      ((-base : ℚ) : ℝ) * x - ((2 * turns : ℚ) : ℝ) * Real.pi := by
    push_cast
    ring
  rw [he]
  exact h

/-- Shared enclosure of one base-point weight and one residual frequency. -/
structure DirichletAtomInterval where
  weight : ComplexInterval
  residual : IntervalRat

/-- Evaluate a positive Dirichlet atom; all scalar coefficients are prepared only once. -/
def dirichletAtomInterval (c : SharedTaylorIntervals) (P : IntervalRat)
    (base radius : ℚ) (n : ℕ) (bin turns : ℤ) : DirichletAtomInterval :=
  let L := c.log n
  let amplitude := c.exp (IntervalRat.scale (-1 / 2) L)
  let phase := dirichletReducedPhase L P base turns
  ⟨⟨IntervalRat.mul amplitude (c.cos phase), IntervalRat.mul amplitude (c.sin phase)⟩,
    IntervalRat.sub (IntervalRat.scale (-radius) L) (IntervalRat.singleton bin)⟩

/-- Soundness includes the actual complex power and the exact chosen-bin residual. -/
theorem dirichletAtomInterval_sound {c : SharedTaylorIntervals} (hc : c.Prepared)
    {P : IntervalRat} (hpi : Real.pi ∈ P) (base radius : ℚ)
    (n : ℕ) (hn : 0 < n) (bin turns : ℤ) :
    1 / (n : ℂ) ^ ((1 / 2 : ℂ) + (base : ℂ) * I) ∈
        (dirichletAtomInterval c P base radius n bin turns).weight ∧
      -(radius : ℝ) * Real.log n - bin ∈
        (dirichletAtomInterval c P base radius n bin turns).residual := by
  have hlog : Real.log (n : ℝ) ∈ c.log n := by
    simpa using SharedTaylorIntervals.mem_log hc (by exact_mod_cast hn : (0 : ℚ) < n)
  have hamp := SharedTaylorIntervals.mem_exp hc (IntervalRat.mem_scale (-1 / 2) hlog)
  have hphase := mem_dirichletReducedPhase hlog hpi base turns
  have hcos := SharedTaylorIntervals.mem_cos hc hphase
  have hsin := SharedTaylorIntervals.mem_sin hc hphase
  rw [Real.cos_sub_int_mul_two_pi] at hcos
  rw [Real.sin_sub_int_mul_two_pi] at hsin
  have he : 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + (base : ℂ) * I) =
      Complex.exp (((-(Real.log n) / 2 : ℝ) : ℂ) +
        ((-(base : ℝ) * Real.log n : ℝ) : ℂ) * I) := by
    rw [one_div, ← cpow_neg,
      cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by omega : n ≠ 0))]
    congr 1
    rw [← ofReal_natCast n, ← ofReal_log (Nat.cast_nonneg n)]
    push_cast
    ring
  constructor
  · rw [he]
    change (Complex.exp _).re ∈ IntervalRat.mul _ _ ∧
      (Complex.exp _).im ∈ IntervalRat.mul _ _
    constructor
    · simpa only [Complex.exp_re, Complex.add_re, Complex.mul_re, Complex.add_im,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one, one_mul,
        Rat.cast_div, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, div_eq_mul_inv,
        Rat.cast_inv, neg_mul, mul_neg, neg_zero, mul_comm] using IntervalRat.mem_mul hamp hcos
    · simpa only [Complex.exp_im, Complex.add_re, Complex.mul_re, Complex.add_im,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one, one_mul,
        Rat.cast_div, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, div_eq_mul_inv,
        Rat.cast_inv, neg_mul, mul_neg, neg_zero, mul_comm] using IntervalRat.mem_mul hamp hsin
  · have h := IntervalRat.mem_sub (IntervalRat.mem_scale (-radius) hlog)
      (IntervalRat.mem_singleton (bin : ℚ))
    simpa [dirichletAtomInterval] using h

end PrimeFactorUnimodality
