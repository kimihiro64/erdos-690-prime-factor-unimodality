import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.GroupedExponential

/-! # Shared exponential evaluation interfaces and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset

variable {ι κ : Type*} [DecidableEq κ]

example (S : Finset ι) (B : Finset κ) (bin : ι → κ)
    (w : ι → ℂ) (f : ι → ℝ) (c : κ → ℝ)
    (hbin : ∀ n ∈ S, bin n ∈ B) (v : ℝ) :
    (∑ n ∈ S, w n * exp (I * ((v * f n : ℝ) : ℂ))) =
      ∑ b ∈ B, exp (I * ((v * c b : ℝ) : ℂ)) *
        ∑ n ∈ S.filter (fun n => bin n = b),
          w n * exp (I * ((v * (f n - c b) : ℝ) : ℂ)) := by
  exact Complex.expSum_eq_grouped S B bin w f c hbin v

example (S : Finset ι) (B : Finset κ) (bin : ι → κ)
    (w : ι → ℂ) (f : ι → ℝ) (c : κ → ℝ) (hbin : ∀ n ∈ S, bin n ∈ B)
    {a v : ℝ} (ha : 0 ≤ a) (h : ∀ n ∈ S, |v * (f n - c (bin n))| ≤ a) (m : ℕ) :
    ‖(∑ n ∈ S, w n * exp (I * ((v * f n : ℝ) : ℂ))) -
      groupedExpPolynomial S B bin w f c m v‖ ≤
        (∑ n ∈ S, ‖w n‖) * (a ^ m * Real.exp a) := by
  exact Complex.norm_expSum_sub_grouped_le S B bin w f c hbin ha h m

example (x : ℝ) : |x - (⌊x + 1 / 2⌋ : ℤ)| ≤ (1 / 2 : ℝ) := by
  exact Complex.abs_sub_nearestInt_le x

example (S : Finset ι) (w : ι → ℂ) (f : ι → ℝ)
    {v : ℝ} (hv : |v| ≤ 1) (m : ℕ) :
    ‖(∑ n ∈ S, w n * exp (I * ((v * f n : ℝ) : ℂ))) -
      groupedExpPolynomial S (S.image (fun n => ⌊f n + 1 / 2⌋))
        (fun n => ⌊f n + 1 / 2⌋) w f (fun k : ℤ => k) m v‖ ≤
      (∑ n ∈ S, ‖w n‖) * ((1 / 2 : ℝ) ^ m * Real.exp (1 / 2)) := by
  exact Complex.norm_expSum_sub_nearestGrouped_le S w f hv m

example : |(1 / 2 : ℝ) - (⌊(1 / 2 : ℝ) + 1 / 2⌋ : ℤ)| = 1 / 2 := by norm_num

example : |(-1 / 2 : ℝ) - (⌊(-1 / 2 : ℝ) + 1 / 2⌋ : ℤ)| = 1 / 2 := by norm_num

example (B : Finset κ) (bin : ι → κ) (w : ι → ℂ) (f : ι → ℝ) (c : κ → ℝ)
    (m : ℕ) (v : ℝ) : groupedExpPolynomial ∅ B bin w f c m v = 0 := by
  simp [groupedExpPolynomial, expSumPolynomial, expSumMoment]

end

end PrimeFactorUnimodality.Tests
