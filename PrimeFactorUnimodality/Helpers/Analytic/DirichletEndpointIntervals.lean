import PrimeFactorUnimodality.Helpers.Analytic.DirichletAtomIntervals

/-! # Shared endpoint powers at enclosed real heights

The endpoint logarithm and amplitude are computed once for a whole grid.
Each sample evaluates only its reduced phase, accepting an interval height
so that exact Fourier heights involving pi are included without rounding
them silently to rational values.
-/

namespace PrimeFactorUnimodality

open Complex LeanCert.Core

/-- Height-independent enclosures shared by every correction in a grid block. -/
structure DirichletEndpointIntervals where
  cutoff : ℕ
  logarithm : IntervalRat
  amplitude : IntervalRat

namespace DirichletEndpointIntervals

/-- Both enclosures describe the same positive endpoint. -/
def Valid (d : DirichletEndpointIntervals) : Prop :=
  0 < d.cutoff ∧ Real.log d.cutoff ∈ d.logarithm ∧
    Real.exp (-Real.log d.cutoff / 2) ∈ d.amplitude

/-- Compute the logarithm once and reuse it for the amplitude. -/
def prepare (c : SharedTaylorIntervals) (N : ℕ) : DirichletEndpointIntervals :=
  let L := c.log N
  ⟨N, L, c.exp (IntervalRat.scale (-1 / 2) L)⟩

/-- Shared scalar preparation supplies the actual endpoint enclosures. -/
theorem prepare_valid {c : SharedTaylorIntervals} (hc : c.Prepared)
    (N : ℕ) (hN : 0 < N) : (prepare c N).Valid := by
  have hlog : Real.log (N : ℝ) ∈ c.log N := by
    simpa using SharedTaylorIntervals.mem_log hc (by exact_mod_cast hN : (0 : ℚ) < N)
  refine ⟨hN, hlog, ?_⟩
  simpa [prepare, div_eq_mul_inv, mul_comm] using
    SharedTaylorIntervals.mem_exp hc (IntervalRat.mem_scale (-1 / 2) hlog)

/-- A reduced phase interval retains the exact real height and every integer period. -/
def phase (d : DirichletEndpointIntervals) (P T : IntervalRat) (turns : ℤ) : IntervalRat :=
  IntervalRat.sub (IntervalRat.scale (-1) (IntervalRat.mul T d.logarithm))
    (IntervalRat.scale (2 * turns) P)

/-- Only two short trigonometric evaluations are repeated at each grid point. -/
def weight (d : DirichletEndpointIntervals) (c : SharedTaylorIntervals)
    (P T : IntervalRat) (turns : ℤ) : ComplexInterval :=
  let H := d.phase P T turns
  ⟨IntervalRat.mul d.amplitude (c.cos H), IntervalRat.mul d.amplitude (c.sin H)⟩

/-- The full integer-period phase shift is contained without assuming rational heights. -/
theorem mem_phase {d : DirichletEndpointIntervals} (hd : d.Valid)
    {P T : IntervalRat} (hpi : Real.pi ∈ P) {t : ℝ} (ht : t ∈ T) (turns : ℤ) :
    -t * Real.log d.cutoff - (turns : ℝ) * (2 * Real.pi) ∈ d.phase P T turns := by
  have h := IntervalRat.mem_sub
    (IntervalRat.mem_scale (-1) (IntervalRat.mem_mul ht hd.2.1))
    (IntervalRat.mem_scale (2 * turns) hpi)
  simpa [phase, neg_mul, mul_assoc, mul_left_comm] using h

/-- The computed rectangle encloses the actual critical-line endpoint power. -/
theorem mem_weight {d : DirichletEndpointIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {P T : IntervalRat}
    (hpi : Real.pi ∈ P) {t : ℝ} (ht : t ∈ T) (turns : ℤ) :
    1 / (d.cutoff : ℂ) ^ ((1 / 2 : ℂ) + t * I) ∈ d.weight c P T turns := by
  have hphase := mem_phase hd hpi ht turns
  have hcos := SharedTaylorIntervals.mem_cos hc hphase
  have hsin := SharedTaylorIntervals.mem_sin hc hphase
  rw [Real.cos_sub_int_mul_two_pi] at hcos
  rw [Real.sin_sub_int_mul_two_pi] at hsin
  have he : 1 / (d.cutoff : ℂ) ^ ((1 / 2 : ℂ) + t * I) =
      Complex.exp (((-Real.log d.cutoff / 2 : ℝ) : ℂ) +
        ((-t * Real.log d.cutoff : ℝ) : ℂ) * I) := by
    rw [one_div, ← cpow_neg,
      cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by have := hd.1; omega))]
    congr 1
    rw [← ofReal_natCast d.cutoff, ← ofReal_log (Nat.cast_nonneg d.cutoff)]
    push_cast
    ring
  rw [he]
  constructor
  · simpa only [Complex.exp_re, Complex.add_re, Complex.mul_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one, one_mul, weight] using
      IntervalRat.mem_mul hd.2.2 hcos
  · simpa only [Complex.exp_im, Complex.add_re, Complex.mul_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one, one_mul, weight] using
      IntervalRat.mem_mul hd.2.2 hsin

end DirichletEndpointIntervals

end PrimeFactorUnimodality
