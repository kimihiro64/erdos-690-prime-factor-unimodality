import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 105 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10007 : Nat.Prime 10007 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10007 10006 1 5 [2, 5003]
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
    · apply IsUnit.of_mul_eq_one (5003 : ZMod 10007)
      decide
    · apply IsUnit.of_mul_eq_one (417 : ZMod 10007)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10009 : Nat.Prime 10009 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10009 10008 1 11 [2, 2, 2, 3, 3, 139]
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
    · apply IsUnit.of_mul_eq_one (5004 : ZMod 10009)
      decide
    · apply IsUnit.of_mul_eq_one (3684 : ZMod 10009)
      decide
    · apply IsUnit.of_mul_eq_one (578 : ZMod 10009)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10037 : Nat.Prime 10037 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10037 10036 1 2 [2, 2, 13, 193]
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
    · apply IsUnit.of_mul_eq_one (5018 : ZMod 10037)
      decide
    · apply IsUnit.of_mul_eq_one (7013 : ZMod 10037)
      decide
    · apply IsUnit.of_mul_eq_one (8757 : ZMod 10037)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10039 : Nat.Prime 10039 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10039 10038 1 3 [2, 3, 7, 239]
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
    · apply IsUnit.of_mul_eq_one (5019 : ZMod 10039)
      decide
    · apply IsUnit.of_mul_eq_one (2102 : ZMod 10039)
      decide
    · apply IsUnit.of_mul_eq_one (4557 : ZMod 10039)
      decide
    · apply IsUnit.of_mul_eq_one (468 : ZMod 10039)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10061 : Nat.Prime 10061 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10061 10060 1 3 [2, 2, 5, 503]
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
    · apply IsUnit.of_mul_eq_one (5030 : ZMod 10061)
      decide
    · apply IsUnit.of_mul_eq_one (8053 : ZMod 10061)
      decide
    · apply IsUnit.of_mul_eq_one (9565 : ZMod 10061)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10067 : Nat.Prime 10067 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10067 10066 1 2 [2, 7, 719]
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
    · apply IsUnit.of_mul_eq_one (5033 : ZMod 10067)
      decide
    · apply IsUnit.of_mul_eq_one (4295 : ZMod 10067)
      decide
    · apply IsUnit.of_mul_eq_one (3234 : ZMod 10067)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10069 : Nat.Prime 10069 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10069 10068 1 2 [2, 2, 3, 839]
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
    · apply IsUnit.of_mul_eq_one (5034 : ZMod 10069)
      decide
    · apply IsUnit.of_mul_eq_one (8500 : ZMod 10069)
      decide
    · apply IsUnit.of_mul_eq_one (986 : ZMod 10069)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10079 : Nat.Prime 10079 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10079 10078 1 11 [2, 5039]
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
    · apply IsUnit.of_mul_eq_one (5039 : ZMod 10079)
      decide
    · apply IsUnit.of_mul_eq_one (84 : ZMod 10079)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 9973) (q := 10007) (by exact lowPrime_10007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10007) (q := 10009) (by exact lowPrime_10009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10009) (q := 10037) (by exact lowPrime_10037) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10037) (q := 10039) (by exact lowPrime_10039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10039) (q := 10061) (by exact lowPrime_10061) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10061) (q := 10067) (by exact lowPrime_10067) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10067) (q := 10069) (by exact lowPrime_10069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10069) (q := 10079) (by exact lowPrime_10079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part02_chain :
    DusartPrimeRowsChain 9973 10078 dusartPrimeRows_9901_10426_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]
