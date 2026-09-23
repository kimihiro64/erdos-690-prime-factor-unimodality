import PrimeFactorUnimodality.Helpers.Analytic.MossinghoffTrudgianPolynomial

/-! # Exact coefficient signs and rational bounds for the degree-sixteen polynomial

Check one finite rational family against the exact generating decimals.
The real inequalities follow by a shared cast, not repeated real arithmetic.
These finite rational calculations complement the already proved global
trigonometric nonnegativity; they do not assume a zero-free region.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Finset Real

/-- Computable normalization of the exact rational generating sequence. -/
def mossinghoffTrudgianEnergyRat : ℚ := ∑ j ∈ range 17, mossinghoffTrudgianGeneratorRat j ^ 2

/-- A linear rational correlation row; the constant coefficient is normalized separately. -/
def mossinghoffTrudgianCoefficientRat (k : ℕ) : ℚ :=
  if k = 0 then 1 else
    (2 * ∑ j ∈ range (17 - k), mossinghoffTrudgianGeneratorRat j *
      mossinghoffTrudgianGeneratorRat (j + k)) / mossinghoffTrudgianEnergyRat

/-- Rational normalization represents exactly the previously defined real energy. -/
theorem mossinghoffTrudgianEnergyRat_cast :
    (mossinghoffTrudgianEnergyRat : ℝ) = mossinghoffTrudgianEnergy := by
  simp [mossinghoffTrudgianEnergyRat, mossinghoffTrudgianEnergy, mossinghoffTrudgianGenerator]

/-- Every rational row represents the actual coefficient, including the constant row. -/
theorem mossinghoffTrudgianCoefficientRat_cast (k : ℕ) :
    (mossinghoffTrudgianCoefficientRat k : ℝ) = mossinghoffTrudgianCoefficient k := by
  by_cases hk : k = 0
  · simp [hk, mossinghoffTrudgianCoefficientRat]
  rw [mossinghoffTrudgianCoefficient_pos_frequency (Nat.pos_of_ne_zero hk)]
  simp [mossinghoffTrudgianCoefficientRat, hk, mossinghoffTrudgianGenerator,
    mossinghoffTrudgianEnergyRat_cast]

/-- The entire finite coefficient family has one kernel-checked sign certificate. -/
theorem mossinghoffTrudgianCoefficientRat_nonneg :
    ∀ k : Fin 17, 0 ≤ mossinghoffTrudgianCoefficientRat k := by
  decide +kernel

/-- Every coefficient in the actual finite polynomial is nonnegative. -/
theorem mossinghoffTrudgianCoefficient_nonneg {k : ℕ} (hk : k < 17) :
    0 ≤ mossinghoffTrudgianCoefficient k := by
  rw [← mossinghoffTrudgianCoefficientRat_cast]
  exact_mod_cast mossinghoffTrudgianCoefficientRat_nonneg ⟨k, hk⟩

/-- The first harmonic has a strictly positive rational lower bound. -/
theorem mossinghoffTrudgianCoefficient_one_bounds :
    (1741 / 1000 : ℝ) ≤ mossinghoffTrudgianCoefficient 1 ∧
      mossinghoffTrudgianCoefficient 1 ≤ (1742 / 1000 : ℝ) := by
  have h : (1741 / 1000 : ℚ) ≤ mossinghoffTrudgianCoefficientRat 1 ∧
      mossinghoffTrudgianCoefficientRat 1 ≤ (1742 / 1000 : ℚ) := by decide +kernel
  rw [← mossinghoffTrudgianCoefficientRat_cast]
  constructor
  · simpa using (Rat.cast_le (K := ℝ)).mpr h.1
  · simpa using (Rat.cast_le (K := ℝ)).mpr h.2

/-- The first harmonic can be supplied directly to the zero-free bootstrap. -/
theorem mossinghoffTrudgianCoefficient_one_pos : 0 < mossinghoffTrudgianCoefficient 1 :=
  lt_of_lt_of_le (by norm_num) mossinghoffTrudgianCoefficient_one_bounds.1

/-- The total mass is bounded without a double sum of correlations. -/
theorem sum_mossinghoffTrudgianCoefficient_bounds :
    (4523 / 1000 : ℝ) ≤ (∑ k ∈ range 17, mossinghoffTrudgianCoefficient k) ∧
      (∑ k ∈ range 17, mossinghoffTrudgianCoefficient k) ≤ (4524 / 1000 : ℝ) := by
  have h : (4523 / 1000 : ℚ) ≤ (∑ k ∈ range 17, mossinghoffTrudgianCoefficientRat k) ∧
      (∑ k ∈ range 17, mossinghoffTrudgianCoefficientRat k) ≤ (4524 / 1000 : ℚ) := by
    decide +kernel
  simp_rw [← mossinghoffTrudgianCoefficientRat_cast]
  constructor
  · simpa using (Rat.cast_le (K := ℝ)).mpr h.1
  · simpa using (Rat.cast_le (K := ℝ)).mpr h.2

/-- The zero harmonic is removed exactly from the leading logarithmic mass. -/
theorem sum_mossinghoffTrudgianCoefficient_erase_zero_bounds :
    (3523 / 1000 : ℝ) ≤ (∑ k ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient k) ∧
      (∑ k ∈ (range 17).erase 0, mossinghoffTrudgianCoefficient k) ≤ (3524 / 1000 : ℝ) := by
  have he := Finset.add_sum_erase (range 17) mossinghoffTrudgianCoefficient
    (show 0 ∈ range 17 by decide)
  rw [mossinghoffTrudgianCoefficient_zero] at he
  obtain ⟨hlo, hhi⟩ := sum_mossinghoffTrudgianCoefficient_bounds
  constructor <;> linarith

end

end PrimeFactorUnimodality
