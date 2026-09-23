import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.ExponentialMoments

/-! # Shared exponential evaluation interfaces and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset

variable {ι κ : Type*} [DecidableEq κ]

example (S : Finset ι) (w : ι → ℂ) (r : ι → ℝ)
    (m : ℕ) (v : ℝ) :
    expSumPolynomial S w r m v =
      ∑ n ∈ S, w n * ∑ j ∈ range m, (I * ((v * r n : ℝ) : ℂ)) ^ j / j.factorial := by
  exact Complex.expSumPolynomial_eq_sum S w r m v

example {v r a : ℝ} (ha : 0 ≤ a)
    (h : |v * r| ≤ a) (m : ℕ) :
    ‖exp (I * ((v * r : ℝ) : ℂ)) -
      ∑ j ∈ range m, (I * ((v * r : ℝ) : ℂ)) ^ j / j.factorial‖ ≤
        a ^ m * Real.exp a := by
  exact Complex.norm_exp_imaginary_sub_sum_le ha h m

example (S : Finset ι) (w : ι → ℂ) (r : ι → ℝ)
    {a v : ℝ} (ha : 0 ≤ a) (h : ∀ n ∈ S, |v * r n| ≤ a) (m : ℕ) :
    ‖(∑ n ∈ S, w n * exp (I * ((v * r n : ℝ) : ℂ))) -
      expSumPolynomial S w r m v‖ ≤
        (∑ n ∈ S, ‖w n‖) * (a ^ m * Real.exp a) := by
  exact Complex.norm_expSum_sub_polynomial_le S w r ha h m

example (S : Finset ι) (w : ι → ℂ) (r : ι → ℝ)
    (m : ℕ) (v : ℝ) (c : ℕ → ℂ) (ε : ℕ → ℝ)
    (hc : ∀ j ∈ range m, ‖expSumMoment S w r j - c j‖ ≤ ε j) :
    ‖expSumPolynomial S w r m v - ∑ j ∈ range m, c j * (v : ℂ) ^ j‖ ≤
      ∑ j ∈ range m, ε j * |v| ^ j := by
  exact Complex.norm_expSumPolynomial_sub_rounded_le S w r m v c ε hc

example (w : ι → ℂ) (r : ι → ℝ) (m : ℕ) (v : ℝ) :
    expSumPolynomial ∅ w r m v = 0 := by
  simp [expSumPolynomial, expSumMoment]

example (S : Finset ι) (w : ι → ℂ) (r : ι → ℝ) (v : ℝ) :
    expSumPolynomial S w r 0 v = 0 := by simp [expSumPolynomial]

example (S : Finset ι) (w : ι → ℂ) (r : ι → ℝ) (v : ℝ) :
    expSumPolynomial S w r 1 v = ∑ n ∈ S, w n := by
  simp [expSumPolynomial, expSumMoment]

end

end PrimeFactorUnimodality.Tests
