import PrimeFactorUnimodality.Helpers.Analytic.ZetaGroupedData

/-! # One Dirichlet atom for the complete short Euler correction

Factoring out the endpoint power leaves only a reciprocal and a short
Bernoulli polynomial. Its rising factors can be evaluated successively,
without recomputing products or powers at each order. The complete Euler
remainder is unchanged and remains part of the existing zeta error bound.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Finset Polynomial

/-- The endpoint and every Bernoulli correction share one complex power. -/
theorem zetaEulerCorrection_eq_factored (N m : ℕ) (hN : 0 < N) (s : ℂ) :
    zetaEulerCorrection N s m = (1 / (N : ℂ) ^ s) *
      ((N : ℂ) / (s - 1) - 1 / 2 +
        ∑ j ∈ range m, (bernoulliNormalizedReal (j + 2) 0 : ℂ) *
          zetaRisingFactor s (j + 1) / (N : ℂ) ^ (j + 1)) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold zetaEulerCorrection
  rw [cpow_sub _ _ hN', cpow_one, cpow_neg, mul_add, mul_sum]
  congr 1
  · rw [show (1 - s) = -(s - 1) by ring]
    simp only [div_neg]
    ring
  · apply sum_congr rfl
    intro j hj
    rw [cpow_sub _ _ hN', cpow_neg, cpow_natCast]
    ring

/-- Normalize each successive rising factor by the next endpoint power. -/
theorem zetaRisingFactor_div_pow_succ (N k : ℕ) (s : ℂ) :
    zetaRisingFactor s (k + 1) / (N : ℂ) ^ (k + 1) =
      (zetaRisingFactor s k / (N : ℂ) ^ k) * (s + (k : ℂ)) / N := by
  rw [zetaRisingFactor_succ, pow_succ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- List form exposes the linear recurrence order of the short Bernoulli sum. -/
theorem zetaEulerCorrection_eq_list (N m : ℕ) (hN : 0 < N) (s : ℂ) :
    zetaEulerCorrection N s m = (1 / (N : ℂ) ^ s) *
      ((N : ℂ) / (s - 1) - 1 / 2 +
        ((List.range' 1 m).map (fun j =>
          (bernoulliNormalizedReal (j + 1) 0 : ℂ) *
            (zetaRisingFactor s j / (N : ℂ) ^ j))).sum) := by
  rw [zetaEulerCorrection_eq_factored N m hN]
  congr 2
  rw [List.range'_eq_map_range, List.map_map,
    ← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range, Function.comp_def]
  apply sum_congr rfl
  intro j hj
  simp only [Nat.add_comm 1 j, Nat.add_assoc, mul_div_assoc]

end

end PrimeFactorUnimodality
