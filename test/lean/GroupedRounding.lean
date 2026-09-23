import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.GroupedRounding

/-! # Shared exponential evaluation interfaces and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset

variable {ι κ : Type*} [DecidableEq κ]

example {p : ℂ} (hp : ‖p‖ = 1) (z q a : ℂ) :
    ‖p * z - a * q‖ ≤ ‖z - q‖ + ‖q‖ * ‖p - a‖ := by
  exact Complex.norm_unit_mul_sub_mul_le hp z q a

example
    (S : Finset ι) (B : Finset κ) (bin : ι → κ) (w : ι → ℂ) (f : ι → ℝ) (c : κ → ℝ)
    (m : ℕ) (v : ℝ) (a : κ → ℕ → ℂ) (p : κ → ℂ) (ε : κ → ℕ → ℝ) (δ : κ → ℝ)
    (ha : ∀ b ∈ B, ∀ j ∈ range m,
      ‖expSumMoment (S.filter (fun n => bin n = b)) w (fun n => f n - c b) j - a b j‖ ≤ ε b j)
    (hp : ∀ b ∈ B, ‖exp (I * ((v * c b : ℝ) : ℂ)) - p b‖ ≤ δ b) :
    ‖groupedExpPolynomial S B bin w f c m v -
      ∑ b ∈ B, p b * ∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ ≤
      ∑ b ∈ B, ((∑ j ∈ range m, ε b j * |v| ^ j) +
        ‖∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ * δ b) := by
  exact Complex.norm_groupedExpPolynomial_sub_rounded_le S B bin w f c m v a p ε δ ha hp

example
    (S : Finset ι) (B : Finset κ) (bin : ι → κ) (w : ι → ℂ) (f : ι → ℝ) (c : κ → ℝ)
    (hbin : ∀ n ∈ S, bin n ∈ B) {A v : ℝ} (hA : 0 ≤ A)
    (hres : ∀ n ∈ S, |v * (f n - c (bin n))| ≤ A)
    (m : ℕ) (a : κ → ℕ → ℂ) (p : κ → ℂ) (ε : κ → ℕ → ℝ) (δ : κ → ℝ)
    (ha : ∀ b ∈ B, ∀ j ∈ range m,
      ‖expSumMoment (S.filter (fun n => bin n = b)) w (fun n => f n - c b) j - a b j‖ ≤ ε b j)
    (hp : ∀ b ∈ B, ‖exp (I * ((v * c b : ℝ) : ℂ)) - p b‖ ≤ δ b) :
    ‖(∑ n ∈ S, w n * exp (I * ((v * f n : ℝ) : ℂ))) -
      ∑ b ∈ B, p b * ∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ ≤
      (∑ n ∈ S, ‖w n‖) * (A ^ m * Real.exp A) +
        ∑ b ∈ B, ((∑ j ∈ range m, ε b j * |v| ^ j) +
          ‖∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ * δ b) := by
  exact Complex.norm_expSum_sub_roundedGrouped_le S B bin w f c hbin hA hres m a p ε δ ha hp



end

end PrimeFactorUnimodality.Tests
