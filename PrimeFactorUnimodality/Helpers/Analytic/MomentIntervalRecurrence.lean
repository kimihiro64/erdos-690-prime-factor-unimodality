import PrimeFactorUnimodality.Helpers.Analytic.ComplexInterval
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.ExponentialMoments

/-! # Shared interval recurrence for Taylor moments

Each successive moment needs one imaginary multiplication and rational
scaling. The initial atom is evaluated once; factorials and powers are not
recomputed independently for every requested order. The same recurrence can
resume at a checked outward-rounded checkpoint.
-/

namespace PrimeFactorUnimodality.ComplexInterval

open Complex LeanCert.Core

/-- One moment transition, with a shared residual-frequency interval. -/
def momentStep (W : ComplexInterval) (R : IntervalRat) (j : ℕ) : ComplexInterval :=
  scale (1 / (j + 1 : ℚ)) (mul W (imag R))

/-- Retain consecutive moment enclosures, starting at an arbitrary checkpoint order. -/
def moments (W : ComplexInterval) (R : IntervalRat) (start : ℕ) : ℕ → List ComplexInterval
  | 0 => []
  | count + 1 => W :: moments (momentStep W R start) R (start + 1) count

/-- One checked transition encloses the exact next Taylor coefficient. -/
theorem mem_momentStep (w : ℂ) (r : ℝ) (j : ℕ) {W : ComplexInterval} {R : IntervalRat}
    (hw : w * (I * (r : ℂ)) ^ j / (j.factorial : ℂ) ∈ W) (hr : r ∈ R) :
    w * (I * (r : ℂ)) ^ (j + 1) / ((j + 1).factorial : ℂ) ∈ momentStep W R j := by
  rw [taylorMoment_succ]
  have h := mem_scale (1 / (j + 1 : ℚ)) (mem_mul hw (mem_imag hr))
  simpa only [momentStep, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv, one_mul, mul_comm] using h

/-- The entire recurrence encloses consecutive exact atoms, including empty runs. -/
theorem moments_sound (w : ℂ) (r : ℝ) (start count : ℕ)
    {W : ComplexInterval} {R : IntervalRat}
    (hw : w * (I * (r : ℂ)) ^ start / (start.factorial : ℂ) ∈ W) (hr : r ∈ R) :
    List.Forall₂ (fun z J => z ∈ J)
      ((List.range' start count).map (fun j => w * (I * (r : ℂ)) ^ j / (j.factorial : ℂ)))
      (moments W R start count) := by
  induction count generalizing start W with
  | zero => simp [moments]
  | succ count ih =>
    rw [moments, List.range'_succ, List.map_cons]
    exact List.Forall₂.cons hw (ih (start + 1) (mem_momentStep w r start hw hr))

/-- No interval is dropped or duplicated by the recurrence. -/
theorem length_moments (W : ComplexInterval) (R : IntervalRat) (start count : ℕ) :
    (moments W R start count).length = count := by
  induction count generalizing start W with
  | zero => rfl
  | succ count ih => simp [moments, ih]

end PrimeFactorUnimodality.ComplexInterval
