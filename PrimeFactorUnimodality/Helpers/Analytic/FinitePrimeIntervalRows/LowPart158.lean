import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 158 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13831 : Nat.Prime 13831 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13831 13830 1 6 [2, 3, 5, 461]
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
    · apply IsUnit.of_mul_eq_one (6915 : ZMod 13831)
      decide
    · apply IsUnit.of_mul_eq_one (3865 : ZMod 13831)
      decide
    · apply IsUnit.of_mul_eq_one (6077 : ZMod 13831)
      decide
    · apply IsUnit.of_mul_eq_one (6886 : ZMod 13831)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13841 : Nat.Prime 13841 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13841 13840 1 6 [2, 2, 2, 2, 5, 173]
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
    · apply IsUnit.of_mul_eq_one (6920 : ZMod 13841)
      decide
    · apply IsUnit.of_mul_eq_one (9806 : ZMod 13841)
      decide
    · apply IsUnit.of_mul_eq_one (11066 : ZMod 13841)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13859 : Nat.Prime 13859 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13859 13858 1 2 [2, 13, 13, 41]
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
    · apply IsUnit.of_mul_eq_one (6929 : ZMod 13859)
      decide
    · apply IsUnit.of_mul_eq_one (5554 : ZMod 13859)
      decide
    · apply IsUnit.of_mul_eq_one (4087 : ZMod 13859)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13873 : Nat.Prime 13873 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13873 13872 1 5 [2, 2, 2, 2, 3, 17, 17]
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
    · apply IsUnit.of_mul_eq_one (6936 : ZMod 13873)
      decide
    · apply IsUnit.of_mul_eq_one (6970 : ZMod 13873)
      decide
    · apply IsUnit.of_mul_eq_one (4982 : ZMod 13873)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13877 : Nat.Prime 13877 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13877 13876 1 2 [2, 2, 3469]
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
    · apply IsUnit.of_mul_eq_one (6938 : ZMod 13877)
      decide
    · apply IsUnit.of_mul_eq_one (6476 : ZMod 13877)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13879 : Nat.Prime 13879 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13879 13878 1 6 [2, 3, 3, 3, 257]
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
    · apply IsUnit.of_mul_eq_one (6939 : ZMod 13879)
      decide
    · apply IsUnit.of_mul_eq_one (12919 : ZMod 13879)
      decide
    · apply IsUnit.of_mul_eq_one (8004 : ZMod 13879)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13883 : Nat.Prime 13883 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13883 13882 1 2 [2, 11, 631]
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
    · apply IsUnit.of_mul_eq_one (6941 : ZMod 13883)
      decide
    · apply IsUnit.of_mul_eq_one (12425 : ZMod 13883)
      decide
    · apply IsUnit.of_mul_eq_one (441 : ZMod 13883)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13901 : Nat.Prime 13901 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13901 13900 1 2 [2, 2, 5, 5, 139]
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
    · apply IsUnit.of_mul_eq_one (6950 : ZMod 13901)
      decide
    · apply IsUnit.of_mul_eq_one (7565 : ZMod 13901)
      decide
    · apply IsUnit.of_mul_eq_one (436 : ZMod 13901)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13829) (q := 13831) (by exact lowPrime_13831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13831) (q := 13841) (by exact lowPrime_13841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13841) (q := 13859) (by exact lowPrime_13859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13859) (q := 13873) (by exact lowPrime_13873) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13873) (q := 13877) (by exact lowPrime_13877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13877) (q := 13879) (by exact lowPrime_13879) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13879) (q := 13883) (by exact lowPrime_13883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13883) (q := 13901) (by exact lowPrime_13901) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part07_chain :
    DusartPrimeRowsChain 13829 13900 dusartPrimeRows_13367_14050_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]
