import PrimeFactorUnimodality.Helpers.Analytic.PlattDirichletInputs
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.CyclicConvolution

set_option autoImplicit false

/-! # Shared convolution assembly of the finite Dirichlet Taylor columns

Each weight and residual power is accumulated once in its assigned bucket.
All output frequencies then use correlations with the shared derivative
columns, evaluated by FFTs. The exact algebra keeps collisions and circular
indexing; the separate input-error theorem must still justify each column's
actual frequency and its logarithmic-shift residual, including wraparound.
-/

open Finset
open scoped Nat

namespace PrimeFactorUnimodality

noncomputable section

variable {N : ℕ} [NeZero N]

/-- One shared coefficient array for each Taylor order. -/
def plattDirichletTaylorBuckets (J : ℕ) (bin : ℕ → ZMod N) (c : ℕ → ℂ)
    (w : ℕ → ℝ) (r : ℕ) : ZMod N → ℂ :=
  ZMod.bucketCoefficients (range J) bin (fun n => c n * ((w n ^ r / (r ! : ℝ) : ℝ) : ℂ))

/-- The exact finite prefix is the sum of shared cyclic correlations. -/
theorem plattApproxDirichletPrefix_eq_correlations (J K : ℕ) (bin : ℕ → ZMod N)
    (c : ℕ → ℂ) (w : ℕ → ℝ) (Q : ℕ → ZMod N → ℂ) (j : ZMod N) :
    plattApproxDirichletPrefix J K c (fun n r => Q r (j + bin n)) w =
      ∑ r ∈ range K, ZMod.cyclicCorrelation (plattDirichletTaylorBuckets J bin c w r) (Q r) j := by
  simp only [plattApproxDirichletPrefix, plattApproxTaylor, Complex.real_smul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  simpa only [plattDirichletTaylorBuckets, mul_assoc] using
    ZMod.sum_mul_shift_eq_cyclicCorrelation (range J) bin
      (fun n => c n * ((w n ^ r / (r ! : ℝ) : ℝ) : ℂ)) (Q r) j

/-- Every correlation can be evaluated using shared forward transforms and an inverse transform. -/
theorem plattApproxDirichletPrefix_eq_fft_columns (J K : ℕ) (bin : ℕ → ZMod N)
    (c : ℕ → ℂ) (w : ℕ → ℝ) (Q : ℕ → ZMod N → ℂ) (j : ZMod N) :
    plattApproxDirichletPrefix J K c (fun n r => Q r (j + bin n)) w =
      ∑ r ∈ range K, (N : ℂ)⁻¹ * ZMod.dft (fun l =>
        ZMod.dft (plattDirichletTaylorBuckets J bin c w r) (-l) * ZMod.dft (Q r) l) (-j) := by
  rw [plattApproxDirichletPrefix_eq_correlations]
  simp_rw [ZMod.cyclicCorrelation_eq_inv_dft]

/-- Linearity combines all Taylor orders before a single final inverse transform. -/
theorem plattApproxDirichletPrefix_eq_single_inverse (J K : ℕ) (bin : ℕ → ZMod N)
    (c : ℕ → ℂ) (w : ℕ → ℝ) (Q : ℕ → ZMod N → ℂ) (j : ZMod N) :
    plattApproxDirichletPrefix J K c (fun n r => Q r (j + bin n)) w =
      (N : ℂ)⁻¹ * ZMod.dft (fun l => ∑ r ∈ range K,
        ZMod.dft (plattDirichletTaylorBuckets J bin c w r) (-l) * ZMod.dft (Q r) l) (-j) := by
  rw [plattApproxDirichletPrefix_eq_fft_columns]
  simp only [ZMod.dft_apply, smul_eq_mul, mul_sum]
  rw [sum_comm]

/-- Rounded convolution outputs retain each order's arithmetic error in the finite prefix. -/
theorem norm_plattApproxDirichletPrefix_sub_rounded_columns_le (J K : ℕ)
    (bin : ℕ → ZMod N) (c : ℕ → ℂ) (w : ℕ → ℝ) (Q : ℕ → ZMod N → ℂ) (j : ZMod N)
    {z : ℕ → ℂ} {δ : ℕ → ℝ}
    (hz : ∀ r ∈ range K,
      ‖ZMod.cyclicCorrelation (plattDirichletTaylorBuckets J bin c w r) (Q r) j - z r‖ ≤ δ r) :
    ‖plattApproxDirichletPrefix J K c (fun n r => Q r (j + bin n)) w - ∑ r ∈ range K, z r‖ ≤
      ∑ r ∈ range K, δ r := by
  rw [plattApproxDirichletPrefix_eq_correlations, ← sum_sub_distrib]
  exact (norm_sum_le _ _).trans (sum_le_sum hz)

end

end PrimeFactorUnimodality
