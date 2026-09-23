import PrimeFactorUnimodality.Helpers.Analytic.MossinghoffTrudgianBounds

/-! # Exact statement regressions for the endpoint bootstrap increment -/

namespace PrimeFactorUnimodality.Tests

open Finset Real

example :
    (mossinghoffTrudgianEnergyRat : ℝ) = mossinghoffTrudgianEnergy := by
  apply PrimeFactorUnimodality.mossinghoffTrudgianEnergyRat_cast <;> assumption

example (k : ℕ) :
    (mossinghoffTrudgianCoefficientRat k : ℝ) = mossinghoffTrudgianCoefficient k := by
  apply PrimeFactorUnimodality.mossinghoffTrudgianCoefficientRat_cast <;> assumption

example :
    ∀ k : Fin 17, 0 ≤ mossinghoffTrudgianCoefficientRat k := by
  apply PrimeFactorUnimodality.mossinghoffTrudgianCoefficientRat_nonneg <;> assumption

example {k : ℕ} (hk : k < 17) :
    0 ≤ mossinghoffTrudgianCoefficient k := by
  apply PrimeFactorUnimodality.mossinghoffTrudgianCoefficient_nonneg <;> assumption

example :
    (1741 / 1000 : ℝ) ≤ mossinghoffTrudgianCoefficient 1 ∧
      mossinghoffTrudgianCoefficient 1 ≤ (1742 / 1000 : ℝ) := by
  apply PrimeFactorUnimodality.mossinghoffTrudgianCoefficient_one_bounds <;> assumption

example : 0 < mossinghoffTrudgianCoefficient 1 := by
  apply PrimeFactorUnimodality.mossinghoffTrudgianCoefficient_one_pos <;> assumption

example :
    (4523 / 1000 : ℝ) ≤ (∑ k ∈ range 17, mossinghoffTrudgianCoefficient k) ∧
      (∑ k ∈ range 17, mossinghoffTrudgianCoefficient k) ≤ (4524 / 1000 : ℝ) := by
  apply PrimeFactorUnimodality.sum_mossinghoffTrudgianCoefficient_bounds <;> assumption

example :
    (3523 / 1000 : ℝ) ≤ (∑ k ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient k) ∧
      (∑ k ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient k) ≤ (3524 / 1000 : ℝ) := by
  apply PrimeFactorUnimodality.sum_mossinghoffTrudgianCoefficient_erase_zero_bounds <;> assumption

example {k : ℕ} (hk : 17 ≤ k) : mossinghoffTrudgianCoefficient k = 0 := by
  rw [← mossinghoffTrudgianCoefficientRat_cast]
  have hk₀ : k ≠ 0 := by omega
  have hsub : 17 - k = 0 := by omega
  simp [mossinghoffTrudgianCoefficientRat, hk₀, hsub]

example : 0 ≤ mossinghoffTrudgianCoefficient 5 ∧
    0 ≤ mossinghoffTrudgianCoefficient 6 ∧ 0 ≤ mossinghoffTrudgianCoefficient 9 :=
  ⟨mossinghoffTrudgianCoefficient_nonneg (by norm_num),
    mossinghoffTrudgianCoefficient_nonneg (by norm_num),
    mossinghoffTrudgianCoefficient_nonneg (by norm_num)⟩

end PrimeFactorUnimodality.Tests
