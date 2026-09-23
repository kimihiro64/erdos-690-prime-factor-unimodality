import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPhaseEvaluation
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.GroupedGrid

/-! # Shared Fourier traces for the low-zero phase sum

One checked transform per Taylor order supplies every grid output. The error
retains grouping, rounded moments, and transform errors separately. Signed
frequencies and alias collisions use the existing exact scatter-add assembler.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Finset Fourier ZMod

/-- The actual low-zero sum is enclosed by the existing shared radix traces. -/
theorem norm_dusartBoxLowPhaseSum_sub_traces_le (m n degree : ℕ)
    (s u T R : ℝ) (B : Finset ℤ) (bin : RiemannXiDivisorZeroIndex → ℤ)
    (hbin : ∀ z ∈ xiLowHeightIndices T, bin z ∈ B)
    (k : ℤ) {A : ℝ} (hA : 0 ≤ A)
    (hres : ∀ z ∈ xiLowHeightIndices T,
      |(2 * Real.pi * k / (2 ^ n)) *
        (R * (riemannXiDivisorZeroValue z).im - bin z)| ≤ A)
    (a : ℤ → ℕ → ℂ) (ε : ℤ → ℕ → ℝ) (t : ℕ → RadixTrace n)
    (ha : ∀ b ∈ B, ∀ j ∈ range degree,
      ‖expSumMoment ((xiLowHeightIndices T).filter (fun z => bin z = b))
        (dusartBoxZeroCoefficient m s u) (fun z => R * (riemannXiDivisorZeroValue z).im - b)
        j - a b j‖ ≤ ε b j)
    (ht : ∀ j ∈ range degree,
      (t j).Valid (stdAddChar (1 : ZMod (2 ^ n))) (aliasVector n B (fun b => a b j))) :
    ‖dusartBoxLowPhaseSum m s u T (R * (2 * Real.pi * k / (2 ^ n))) -
      ∑ j ∈ range degree, (t j).values[(k : ZMod (2 ^ n)).val]'(val_lt _) *
        ((2 * Real.pi * k / (2 ^ n) : ℝ) : ℂ) ^ j‖ ≤
      ((∑ z ∈ xiLowHeightIndices T, ‖dusartBoxZeroCoefficient m s u z‖) *
        (A ^ degree * Real.exp A) +
        ∑ b ∈ B, ∑ j ∈ range degree, ε b j * |2 * Real.pi * k / (2 ^ n)| ^ j) +
      ∑ j ∈ range degree, (t j).error * |2 * Real.pi * k / (2 ^ n)| ^ j := by
  have hg := norm_dusartBoxLowPhaseSum_sub_grouped_le m s u T R B bin
    (fun b : ℤ => b) hbin hA hres degree a
    (fun b => exp (I * (((2 * Real.pi * k / (2 ^ n)) * b : ℝ) : ℂ)))
    ε (fun _ => 0) ha (fun _ _ => by simp)
  simp only [mul_zero, add_zero] at hg
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (∑ b ∈ B, exp (I * (((2 * Real.pi * k / (2 ^ n)) * b : ℝ) : ℂ)) *
      ∑ j ∈ range degree, a b j * ((2 * Real.pi * k / (2 ^ n) : ℝ) : ℂ) ^ j) _).trans
    (add_le_add hg (norm_exp_polynomial_grid_sub_traces_le n degree B a t ht k))

end

end PrimeFactorUnimodality
