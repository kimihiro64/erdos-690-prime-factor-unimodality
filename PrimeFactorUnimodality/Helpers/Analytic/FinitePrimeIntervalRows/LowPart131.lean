import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 131 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11927 : Nat.Prime 11927 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11927 11926 1 5 [2, 67, 89]
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
    · apply IsUnit.of_mul_eq_one (5963 : ZMod 11927)
      decide
    · apply IsUnit.of_mul_eq_one (5850 : ZMod 11927)
      decide
    · apply IsUnit.of_mul_eq_one (10316 : ZMod 11927)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11933 : Nat.Prime 11933 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11933 11932 1 2 [2, 2, 19, 157]
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
    · apply IsUnit.of_mul_eq_one (5966 : ZMod 11933)
      decide
    · apply IsUnit.of_mul_eq_one (10542 : ZMod 11933)
      decide
    · apply IsUnit.of_mul_eq_one (3072 : ZMod 11933)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11939 : Nat.Prime 11939 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11939 11938 1 2 [2, 47, 127]
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
    · apply IsUnit.of_mul_eq_one (5969 : ZMod 11939)
      decide
    · apply IsUnit.of_mul_eq_one (6685 : ZMod 11939)
      decide
    · apply IsUnit.of_mul_eq_one (440 : ZMod 11939)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11941 : Nat.Prime 11941 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11941 11940 1 10 [2, 2, 3, 5, 199]
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
    · apply IsUnit.of_mul_eq_one (5970 : ZMod 11941)
      decide
    · apply IsUnit.of_mul_eq_one (9024 : ZMod 11941)
      decide
    · apply IsUnit.of_mul_eq_one (5174 : ZMod 11941)
      decide
    · apply IsUnit.of_mul_eq_one (9848 : ZMod 11941)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11953 : Nat.Prime 11953 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11953 11952 1 5 [2, 2, 2, 2, 3, 3, 83]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5976 : ZMod 11953)
      decide
    · apply IsUnit.of_mul_eq_one (9006 : ZMod 11953)
      decide
    · apply IsUnit.of_mul_eq_one (4077 : ZMod 11953)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11959 : Nat.Prime 11959 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11959 11958 1 3 [2, 3, 1993]
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
    · apply IsUnit.of_mul_eq_one (5979 : ZMod 11959)
      decide
    · apply IsUnit.of_mul_eq_one (7717 : ZMod 11959)
      decide
    · apply IsUnit.of_mul_eq_one (10267 : ZMod 11959)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11969 : Nat.Prime 11969 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11969 11968 1 3 [2, 2, 2, 2, 2, 2, 11, 17]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5984 : ZMod 11969)
      decide
    · apply IsUnit.of_mul_eq_one (4751 : ZMod 11969)
      decide
    · apply IsUnit.of_mul_eq_one (8177 : ZMod 11969)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11971 : Nat.Prime 11971 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11971 11970 1 10 [2, 3, 3, 5, 7, 19]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5985 : ZMod 11971)
      decide
    · apply IsUnit.of_mul_eq_one (9722 : ZMod 11971)
      decide
    · apply IsUnit.of_mul_eq_one (10508 : ZMod 11971)
      decide
    · apply IsUnit.of_mul_eq_one (3312 : ZMod 11971)
      decide
    · apply IsUnit.of_mul_eq_one (5504 : ZMod 11971)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11923) (q := 11927) (by exact lowPrime_11927) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11927) (q := 11933) (by exact lowPrime_11933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11933) (q := 11939) (by exact lowPrime_11939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11939) (q := 11941) (by exact lowPrime_11941) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11941) (q := 11953) (by exact lowPrime_11953) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11953) (q := 11959) (by exact lowPrime_11959) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11959) (q := 11969) (by exact lowPrime_11969) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11969) (q := 11971) (by exact lowPrime_11971) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part06_chain :
    DusartPrimeRowsChain 11923 11970 dusartPrimeRows_11503_12096_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12088, dusartPrimeRow_of_explicit_right]
