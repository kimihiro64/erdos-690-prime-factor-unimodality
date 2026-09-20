import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 280 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17881 : Nat.Prime 17881 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17881 17880 1 7 [2, 2, 2, 3, 5, 149]
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
    · apply IsUnit.of_mul_eq_one (8940 : ZMod 17881)
      decide
    · apply IsUnit.of_mul_eq_one (13780 : ZMod 17881)
      decide
    · apply IsUnit.of_mul_eq_one (6375 : ZMod 17881)
      decide
    · apply IsUnit.of_mul_eq_one (15183 : ZMod 17881)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17891 : Nat.Prime 17891 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17891 17890 1 2 [2, 5, 1789]
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
    · apply IsUnit.of_mul_eq_one (8945 : ZMod 17891)
      decide
    · apply IsUnit.of_mul_eq_one (13914 : ZMod 17891)
      decide
    · apply IsUnit.of_mul_eq_one (3113 : ZMod 17891)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17903 : Nat.Prime 17903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17903 17902 1 5 [2, 8951]
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
    · apply IsUnit.of_mul_eq_one (8951 : ZMod 17903)
      decide
    · apply IsUnit.of_mul_eq_one (746 : ZMod 17903)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17909 : Nat.Prime 17909 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17909 17908 1 2 [2, 2, 11, 11, 37]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (8954 : ZMod 17909)
      decide
    · apply IsUnit.of_mul_eq_one (9684 : ZMod 17909)
      decide
    · apply IsUnit.of_mul_eq_one (10438 : ZMod 17909)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17911 : Nat.Prime 17911 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17911 17910 1 3 [2, 3, 3, 5, 199]
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
    · apply IsUnit.of_mul_eq_one (8955 : ZMod 17911)
      decide
    · apply IsUnit.of_mul_eq_one (13623 : ZMod 17911)
      decide
    · apply IsUnit.of_mul_eq_one (7261 : ZMod 17911)
      decide
    · apply IsUnit.of_mul_eq_one (4038 : ZMod 17911)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17921 : Nat.Prime 17921 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17921 17920 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 7]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (8960 : ZMod 17921)
      decide
    · apply IsUnit.of_mul_eq_one (10503 : ZMod 17921)
      decide
    · apply IsUnit.of_mul_eq_one (12499 : ZMod 17921)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17923 : Nat.Prime 17923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17923 17922 1 2 [2, 3, 29, 103]
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
    · apply IsUnit.of_mul_eq_one (8961 : ZMod 17923)
      decide
    · apply IsUnit.of_mul_eq_one (204 : ZMod 17923)
      decide
    · apply IsUnit.of_mul_eq_one (3102 : ZMod 17923)
      decide
    · apply IsUnit.of_mul_eq_one (1634 : ZMod 17923)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17929 : Nat.Prime 17929 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17929 17928 1 11 [2, 2, 2, 3, 3, 3, 83]
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
    · apply IsUnit.of_mul_eq_one (8964 : ZMod 17929)
      decide
    · apply IsUnit.of_mul_eq_one (6911 : ZMod 17929)
      decide
    · apply IsUnit.of_mul_eq_one (841 : ZMod 17929)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17863) (q := 17881) (by exact lowPrime_17881) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17881) (q := 17891) (by exact lowPrime_17891) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17891) (q := 17903) (by exact lowPrime_17903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17903) (q := 17909) (by exact lowPrime_17909) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17909) (q := 17911) (by exact lowPrime_17911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17911) (q := 17921) (by exact lowPrime_17921) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17921) (q := 17923) (by exact lowPrime_17923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17923) (q := 17929) (by exact lowPrime_17929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part10_chain :
    DusartPrimeRowsChain 17863 17928 dusartPrimeRows_17159_18040_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]
