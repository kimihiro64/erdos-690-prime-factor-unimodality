import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.FiniteDensity.Monotonicity
import PrimeFactorUnimodality.Helpers.Unimodality.CoupledRecurrence
import PrimeFactorUnimodality.Proof.Unimodality.Generated.PositiveK3

set_option autoImplicit false

/-! # Unimodality for the first three distinct-prime-factor densities -/

namespace PrimeFactorUnimodality

noncomputable section

private theorem primeAt_one : primeAt 1 = 3 := by
  rw [← show Nat.primeCounting' 3 = 1 by decide]
  exact primeAt_primeCounting' 3 (by decide)

private theorem primeAt_twentyThree : primeAt 23 = 89 := by
  rw [← show Nat.primeCounting' 89 = 23 by decide]
  exact primeAt_primeCounting' 89 (by decide)

private theorem prefixDensity_zero_le_one_at_one :
    prefixDensity 0 1 ≤ prefixDensity 1 1 := by
  rw [prefixDensity, prefixDensity, primeAt_one,
    finiteDensity_perm primesBelow3_perm,
    finiteDensity_perm primesBelow3_perm]
  norm_num [primePrefix3, primePrefix2, finiteDensity]

theorem prefixDensity_one_antitone (i : Nat) (hi : 1 ≤ i) :
    prefixDensity 1 (i + 1) ≤ prefixDensity 1 i := by
  exact (coupled_recurrence_tail
    (prefixDensity 0) (prefixDensity 1) primeRetention 1
    (fun j => ⟨primeRetention_nonneg j, primeRetention_le_one j⟩)
    (fun j => by simpa using prefixDensity_succ 0 j)
    (fun j _ => prefixDensity_zero_antitone j)
    prefixDensity_zero_le_one_at_one).2 i hi

private theorem prefixDensity_one_le_two_at_twentyThree :
    prefixDensity 1 23 ≤ prefixDensity 2 23 := by
  rw [prefixDensity, prefixDensity, primeAt_twentyThree,
    finiteDensity_perm primesBelow89_perm,
    finiteDensity_perm primesBelow89_perm,
    finiteDensity_eq_selectionNumerator_div primePrefix89 primePrefix89_gt_one,
    finiteDensity_eq_selectionNumerator_div primePrefix89 primePrefix89_gt_one,
    ← selectionRowBounded_getD 7 primePrefix89 1 (by omega),
    ← selectionRowBounded_getD 7 primePrefix89 2 (by omega), numericalRow89]
  apply div_le_div_of_nonneg_right (by norm_num)
  positivity

theorem prefixDensity_two_antitone (i : Nat) (hi : 23 ≤ i) :
    prefixDensity 2 (i + 1) ≤ prefixDensity 2 i := by
  exact (coupled_recurrence_tail
    (prefixDensity 1) (prefixDensity 2) primeRetention 23
    (fun j => ⟨primeRetention_nonneg j, primeRetention_le_one j⟩)
    (fun j => by simpa using prefixDensity_succ 1 j)
    (fun j hj => prefixDensity_one_antitone j (by omega))
    prefixDensity_one_le_two_at_twentyThree).2 i hi

theorem primeFactorDensity_nonneg (k i : Nat) :
    0 ≤ primeFactorDensity k i := by
  unfold primeFactorDensity prescribedFactorDensity
  exact div_nonneg (finiteDensity_nonneg _ _) (by positivity)

private theorem primeFactorDensity_two_at_zero :
    primeFactorDensity 2 0 = 0 := by
  have hp : primeAt 0 = 2 := by
    rw [← show Nat.primeCounting' 2 = 0 by decide]
    exact primeAt_primeCounting' 2 (by decide)
  rw [primeFactorDensity, hp]
  unfold prescribedFactorDensity
  rw [finiteDensity_perm primesBelow2_perm]
  norm_num [primePrefix2, finiteDensity]

private theorem primeFactorDensity_three_at_zero :
    primeFactorDensity 3 0 = 0 := by
  have hp : primeAt 0 = 2 := by
    rw [← show Nat.primeCounting' 2 = 0 by decide]
    exact primeAt_primeCounting' 2 (by decide)
  rw [primeFactorDensity, hp]
  unfold prescribedFactorDensity
  rw [finiteDensity_perm primesBelow2_perm]
  norm_num [primePrefix2, finiteDensity]

private theorem primeFactorDensity_three_at_one :
    primeFactorDensity 3 1 = 0 := by
  rw [primeFactorDensity, primeAt_one]
  unfold prescribedFactorDensity
  rw [finiteDensity_perm primesBelow3_perm]
  norm_num [primePrefix3, primePrefix2, finiteDensity]

theorem firstPrimeFactorDensity_isUnimodal :
    IsUnimodal (primeFactorDensity 1) := by
  refine ⟨0, ?_, ?_⟩
  · intro i hi
    omega
  · intro i _
    apply primeFactorDensity_step_le_of_prefixDensity_step_le
    exact prefixDensity_zero_antitone i

theorem secondPrimeFactorDensity_isUnimodal :
    IsUnimodal (primeFactorDensity 2) := by
  refine ⟨1, ?_, ?_⟩
  · intro i hi
    have : i = 0 := by omega
    subst i
    rw [primeFactorDensity_two_at_zero]
    exact primeFactorDensity_nonneg 2 1
  · intro i hi
    apply primeFactorDensity_step_le_of_prefixDensity_step_le
    exact prefixDensity_one_antitone i hi

theorem thirdPrimeFactorDensity_isUnimodal :
    IsUnimodal (primeFactorDensity 3) := by
  refine ⟨2, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · rw [primeFactorDensity_three_at_zero]
      exact primeFactorDensity_nonneg 3 1
    · rw [primeFactorDensity_three_at_one]
      exact primeFactorDensity_nonneg 3 2
  · intro i hi
    by_cases hTail : 23 ≤ i
    · apply primeFactorDensity_step_le_of_prefixDensity_step_le
      exact prefixDensity_two_antitone i hTail
    · exact k3PrimeFactorDensity_finite_descent i hi (by omega)

end

end PrimeFactorUnimodality
