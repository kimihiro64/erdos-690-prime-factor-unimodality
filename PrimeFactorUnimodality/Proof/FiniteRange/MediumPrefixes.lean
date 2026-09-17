import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import PrimeFactorUnimodality.Helpers.PrimeSequence.InitialSegment

set_option autoImplicit false
set_option maxRecDepth 10000

/-! # Initial prime-weight prefixes used by the medium finite range -/

namespace PrimeFactorUnimodality

private theorem primeAt29_eq : primeAt 29 = 113 := by
  rw [← show Nat.primeCounting' 113 = 29 by decide]
  exact primeAt_primeCounting' 113 (by decide)

private theorem primeAt46_eq : primeAt 46 = 211 := by
  rw [← show Nat.primeCounting' 211 = 46 by decide]
  exact primeAt_primeCounting' 211 (by decide)

theorem leadingWeightSum15683_29 :
    leadingWeightSum (primesBelow 15683) 29 = weightSum (primesBelow 113) := by
  rw [leadingWeightSum_eq_weightSum_take]
  have hcount : 29 ≤ Nat.primeCounting' 15683 := by
    rw [← show Nat.primeCounting' 113 = 29 by decide]
    exact Nat.monotone_primeCounting' (by norm_num)
  rw [take_primesBelow_of_prime 15683 29 (by norm_num) hcount, primeAt29_eq]

theorem leadingWeightSum31397_46 :
    leadingWeightSum (primesBelow 31397) 46 = weightSum (primesBelow 211) := by
  rw [leadingWeightSum_eq_weightSum_take]
  have hcount : 46 ≤ Nat.primeCounting' 31397 := by
    rw [← show Nat.primeCounting' 211 = 46 by decide]
    exact Nat.monotone_primeCounting' (by norm_num)
  rw [take_primesBelow_of_prime 31397 46 (by norm_num) hcount, primeAt46_eq]

end PrimeFactorUnimodality
