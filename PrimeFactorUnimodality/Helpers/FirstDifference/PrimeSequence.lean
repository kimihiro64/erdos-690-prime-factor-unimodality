import PrimeFactorUnimodality.Helpers.FiniteDensity.Permutation
import PrimeFactorUnimodality.Helpers.FirstDifference.Threshold
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic
import PrimeFactorUnimodality.Helpers.SymmetricBounds.Positivity

set_option autoImplicit false

/-!
# The first-difference criterion on the indexed prime sequence
-/

namespace PrimeFactorUnimodality

noncomputable section

theorem primeAt_add_primeGap (i : Nat) :
    primeAt i + primeGap i = primeAt (i + 1) := by
  rw [primeGap, Nat.add_sub_of_le]
  exact (primeAt_strictMono (Nat.lt_succ_self i)).le

theorem primeFactorDensity_succ (k i : Nat) :
    primeFactorDensity k (i + 1) =
      prescribedFactorDensity
        (primeAt i :: primesBelow (primeAt i)) k (primeAt (i + 1)) := by
  rw [primeFactorDensity]
  exact prescribedFactorDensity_perm (primesBelow_primeAt_succ_perm i) k
    (primeAt (i + 1))

theorem primeDensityStep_iff_ratio_gap
    (r i : Nat) (hri : r + 1 ≤ i) :
    primeFactorDensity (r + 2) (i + 1) > primeFactorDensity (r + 2) i ↔
      densityRatio (primesBelow (primeAt i)) (r + 1) > (primeGap i + 1 : Nat) := by
  rw [primeFactorDensity_succ, primeFactorDensity]
  rw [← primeAt_add_primeGap i]
  apply densityStep_iff_symmetricRatio_gap
  · exact (one_lt_primeAt i).trans' Nat.zero_lt_one
  · apply finiteDensity_pos
    · exact primesBelow_gt_one (primeAt i)
    · rw [primesBelow_primeAt_length]
      exact hri

theorem primeDensityStep_lt_iff_ratio_lt_gap
    (r i : Nat) (hri : r + 1 ≤ i) :
    primeFactorDensity (r + 2) (i + 1) < primeFactorDensity (r + 2) i ↔
      densityRatio (primesBelow (primeAt i)) (r + 1) < (primeGap i + 1 : Nat) := by
  rw [primeFactorDensity_succ, primeFactorDensity]
  rw [← primeAt_add_primeGap i]
  apply densityStep_lt_iff_symmetricRatio_lt_gap
  · exact (one_lt_primeAt i).trans' Nat.zero_lt_one
  · apply finiteDensity_pos
    · exact primesBelow_gt_one (primeAt i)
    · rw [primesBelow_primeAt_length]
      exact hri

theorem primeDensityStep_le_iff_ratio_le_gap
    (r i : Nat) (hri : r + 1 ≤ i) :
    primeFactorDensity (r + 2) (i + 1) ≤ primeFactorDensity (r + 2) i ↔
      densityRatio (primesBelow (primeAt i)) (r + 1) ≤ (primeGap i + 1 : Nat) := by
  rw [primeFactorDensity_succ, primeFactorDensity]
  rw [← primeAt_add_primeGap i]
  apply densityStep_le_iff_symmetricRatio_le_gap
  · exact (one_lt_primeAt i).trans' Nat.zero_lt_one
  · apply finiteDensity_pos
    · exact primesBelow_gt_one (primeAt i)
    · rw [primesBelow_primeAt_length]
      exact hri

end

end PrimeFactorUnimodality
