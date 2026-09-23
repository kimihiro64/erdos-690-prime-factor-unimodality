import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPhaseGrid

/-! # Actual low-zero phase estimates from shared transforms at signed grid indices -/

open PrimeFactorUnimodality Complex Finset Fourier ZMod

example (m n degree : ℕ) (s u T R : ℝ) (B : Finset ℤ)
    (bin : RiemannXiDivisorZeroIndex → ℤ)
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
      ∑ j ∈ range degree, (t j).error * |2 * Real.pi * k / (2 ^ n)| ^ j :=
  norm_dusartBoxLowPhaseSum_sub_traces_le m n degree s u T R B bin hbin k hA hres a ε t ha ht
