import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.SincExponential
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.SymmetricTruncation

/-! Unit-cell normalization, cutoff endpoints and exactly integrated exponential tails. -/

open MeasureTheory

example : (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Fourier.samplingPhase 0 x) = 1 := by
  simpa using Fourier.integral_samplingPhase 0

example (t : ℝ) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Fourier.samplingPhase (-t) x) =
      (Real.sinc (Real.pi * t) : ℂ) := by
  simpa using Fourier.integral_samplingPhase (-t)

example (f : ℤ → ℂ) : Fourier.symmetricSum f 0 = f 0 := by
  simp [Fourier.symmetricSum]

example (f : ℤ → ℂ) : Fourier.symmetricSum f 1 = f 0 + f 1 + f (-1) := by
  simp [Fourier.symmetricSum, Finset.sum_range_succ]

example {a : ℝ} (ha : 0 < a) :
    (∫ x in (Set.Ioc (0 : ℝ) 0)ᶜ, Real.exp (-a * |x|)) = 2 / a := by
  simpa [div_eq_mul_inv] using Fourier.integral_exp_neg_mul_abs_compl ha (le_refl (0 : ℝ))

example {f : ℤ → ℂ} (hf : Summable f) (M : ℕ) {g : ℕ → ℝ} {S : ℝ} (hg : HasSum g S)
    (hp : ∀ n : ℕ, ‖f (n + M + 1)‖ ≤ g n)
    (hn : ∀ n : ℕ, ‖f (-(n + M + 1))‖ ≤ g n) :
    ‖(∑' n : ℤ, f n) - Fourier.symmetricSum f M‖ ≤ 2 * S :=
  Fourier.norm_tsum_sub_symmetricSum_le hf M hg hp hn
