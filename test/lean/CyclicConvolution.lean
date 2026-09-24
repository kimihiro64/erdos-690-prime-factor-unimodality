import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.CyclicConvolution

/-! Regression checks for normalization, reversal and colliding coefficient buckets. -/

open Finset

example {N : ℕ} [NeZero N] (a b : ZMod N → ℂ) (j : ZMod N) :
    ZMod.cyclicCorrelation a b j = (N : ℂ)⁻¹ *
      ZMod.dft (fun k => ZMod.dft a (-k) * ZMod.dft b k) (-j) :=
  ZMod.cyclicCorrelation_eq_inv_dft a b j

example (a b : ZMod 1 → ℂ) : ZMod.cyclicConvolution a b 0 = a 0 * b 0 := by
  unfold ZMod.cyclicConvolution
  rw [Fintype.sum_unique]
  exact congrArg₂ (fun x y : ZMod 1 => a x * b y)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)

example {N : ℕ} [NeZero N] (a b : ℂ) (j : ZMod N) :
    ZMod.bucketCoefficients (range 2) (fun _ => j) (fun n => if n = 0 then a else b) j =
      a + b := by
  simp [ZMod.bucketCoefficients, sum_range_succ]

example {N : ℕ} [NeZero N] (a b : ℂ) (q : ZMod N → ℂ) (j l : ZMod N) :
    ZMod.cyclicCorrelation
      (ZMod.bucketCoefficients (range 2) (fun _ => l) (fun n => if n = 0 then a else b))
      q j = (a + b) * q (j + l) := by
  rw [← ZMod.sum_mul_shift_eq_cyclicCorrelation]
  simp [sum_range_succ, add_mul]
