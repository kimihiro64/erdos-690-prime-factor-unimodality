import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 118 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10949 : Nat.Prime 10949 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10949 10948 1 2 [2, 2, 7, 17, 23]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5474 : ZMod 10949)
      decide
    · apply IsUnit.of_mul_eq_one (7577 : ZMod 10949)
      decide
    · apply IsUnit.of_mul_eq_one (5820 : ZMod 10949)
      decide
    · apply IsUnit.of_mul_eq_one (10813 : ZMod 10949)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10957 : Nat.Prime 10957 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10957 10956 1 5 [2, 2, 3, 11, 83]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5478 : ZMod 10957)
      decide
    · apply IsUnit.of_mul_eq_one (9908 : ZMod 10957)
      decide
    · apply IsUnit.of_mul_eq_one (7368 : ZMod 10957)
      decide
    · apply IsUnit.of_mul_eq_one (2635 : ZMod 10957)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10973 : Nat.Prime 10973 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10973 10972 1 2 [2, 2, 13, 211]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5486 : ZMod 10973)
      decide
    · apply IsUnit.of_mul_eq_one (1173 : ZMod 10973)
      decide
    · apply IsUnit.of_mul_eq_one (1598 : ZMod 10973)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10979 : Nat.Prime 10979 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10979 10978 1 2 [2, 11, 499]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5489 : ZMod 10979)
      decide
    · apply IsUnit.of_mul_eq_one (5502 : ZMod 10979)
      decide
    · apply IsUnit.of_mul_eq_one (6959 : ZMod 10979)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10987 : Nat.Prime 10987 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10987 10986 1 2 [2, 3, 1831]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5493 : ZMod 10987)
      decide
    · apply IsUnit.of_mul_eq_one (8777 : ZMod 10987)
      decide
    · apply IsUnit.of_mul_eq_one (872 : ZMod 10987)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10993 : Nat.Prime 10993 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10993 10992 1 7 [2, 2, 2, 2, 3, 229]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5496 : ZMod 10993)
      decide
    · apply IsUnit.of_mul_eq_one (7843 : ZMod 10993)
      decide
    · apply IsUnit.of_mul_eq_one (5526 : ZMod 10993)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11003 : Nat.Prime 11003 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11003 11002 1 2 [2, 5501]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (5501 : ZMod 11003)
      decide
    · apply IsUnit.of_mul_eq_one (3668 : ZMod 11003)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11027 : Nat.Prime 11027 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11027 11026 1 2 [2, 37, 149]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5513 : ZMod 11027)
      decide
    · apply IsUnit.of_mul_eq_one (10487 : ZMod 11027)
      decide
    · apply IsUnit.of_mul_eq_one (1519 : ZMod 11027)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 10939) (q := 10949) (by exact lowPrime_10949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10949) (q := 10957) (by exact lowPrime_10957) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10957) (q := 10973) (by exact lowPrime_10973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10973) (q := 10979) (by exact lowPrime_10979) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10979) (q := 10987) (by exact lowPrime_10987) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10987) (q := 10993) (by exact lowPrime_10993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10993) (q := 11003) (by exact lowPrime_11003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11003) (q := 11027) (by exact lowPrime_11027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part01_chain :
    DusartPrimeRowsChain 10939 11026 dusartPrimeRows_10939_11502_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]
