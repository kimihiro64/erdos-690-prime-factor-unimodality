import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 119 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11047 : Nat.Prime 11047 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11047 11046 1 3 [2, 3, 7, 263]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5523 : ZMod 11047)
      decide
    · apply IsUnit.of_mul_eq_one (7928 : ZMod 11047)
      decide
    · apply IsUnit.of_mul_eq_one (4502 : ZMod 11047)
      decide
    · apply IsUnit.of_mul_eq_one (9845 : ZMod 11047)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11057 : Nat.Prime 11057 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11057 11056 1 3 [2, 2, 2, 2, 691]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (5528 : ZMod 11057)
      decide
    · apply IsUnit.of_mul_eq_one (1933 : ZMod 11057)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11059 : Nat.Prime 11059 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11059 11058 1 10 [2, 3, 19, 97]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5529 : ZMod 11059)
      decide
    · apply IsUnit.of_mul_eq_one (1435 : ZMod 11059)
      decide
    · apply IsUnit.of_mul_eq_one (4334 : ZMod 11059)
      decide
    · apply IsUnit.of_mul_eq_one (6582 : ZMod 11059)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11069 : Nat.Prime 11069 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11069 11068 1 2 [2, 2, 2767]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (5534 : ZMod 11069)
      decide
    · apply IsUnit.of_mul_eq_one (738 : ZMod 11069)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11071 : Nat.Prime 11071 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11071 11070 1 3 [2, 3, 3, 3, 5, 41]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5535 : ZMod 11071)
      decide
    · apply IsUnit.of_mul_eq_one (10491 : ZMod 11071)
      decide
    · apply IsUnit.of_mul_eq_one (8769 : ZMod 11071)
      decide
    · apply IsUnit.of_mul_eq_one (3795 : ZMod 11071)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11083 : Nat.Prime 11083 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11083 11082 1 2 [2, 3, 1847]
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
    · apply IsUnit.of_mul_eq_one (5541 : ZMod 11083)
      decide
    · apply IsUnit.of_mul_eq_one (5153 : ZMod 11083)
      decide
    · apply IsUnit.of_mul_eq_one (6685 : ZMod 11083)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11087 : Nat.Prime 11087 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11087 11086 1 5 [2, 23, 241]
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
    · apply IsUnit.of_mul_eq_one (5543 : ZMod 11087)
      decide
    · apply IsUnit.of_mul_eq_one (1844 : ZMod 11087)
      decide
    · apply IsUnit.of_mul_eq_one (4718 : ZMod 11087)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11093 : Nat.Prime 11093 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11093 11092 1 2 [2, 2, 47, 59]
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
    · apply IsUnit.of_mul_eq_one (5546 : ZMod 11093)
      decide
    · apply IsUnit.of_mul_eq_one (7494 : ZMod 11093)
      decide
    · apply IsUnit.of_mul_eq_one (8300 : ZMod 11093)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11027) (q := 11047) (by exact lowPrime_11047) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11047) (q := 11057) (by exact lowPrime_11057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11057) (q := 11059) (by exact lowPrime_11059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11059) (q := 11069) (by exact lowPrime_11069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11069) (q := 11071) (by exact lowPrime_11071) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11071) (q := 11083) (by exact lowPrime_11083) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11083) (q := 11087) (by exact lowPrime_11087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11087) (q := 11093) (by exact lowPrime_11093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part02_chain :
    DusartPrimeRowsChain 11027 11092 dusartPrimeRows_10939_11502_part02 := by
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
