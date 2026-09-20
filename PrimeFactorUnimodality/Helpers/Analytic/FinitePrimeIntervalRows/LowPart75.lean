import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 75 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8053 : Nat.Prime 8053 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8053 8052 1 2 [2, 2, 3, 11, 61]
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
    · apply IsUnit.of_mul_eq_one (4026 : ZMod 8053)
      decide
    · apply IsUnit.of_mul_eq_one (1518 : ZMod 8053)
      decide
    · apply IsUnit.of_mul_eq_one (1992 : ZMod 8053)
      decide
    · apply IsUnit.of_mul_eq_one (5193 : ZMod 8053)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8059 : Nat.Prime 8059 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8059 8058 1 3 [2, 3, 17, 79]
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
    · apply IsUnit.of_mul_eq_one (4029 : ZMod 8059)
      decide
    · apply IsUnit.of_mul_eq_one (6294 : ZMod 8059)
      decide
    · apply IsUnit.of_mul_eq_one (254 : ZMod 8059)
      decide
    · apply IsUnit.of_mul_eq_one (4922 : ZMod 8059)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8069 : Nat.Prime 8069 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8069 8068 1 2 [2, 2, 2017]
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
    · apply IsUnit.of_mul_eq_one (4034 : ZMod 8069)
      decide
    · apply IsUnit.of_mul_eq_one (538 : ZMod 8069)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8081 : Nat.Prime 8081 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8081 8080 1 3 [2, 2, 2, 2, 5, 101]
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
    · apply IsUnit.of_mul_eq_one (4040 : ZMod 8081)
      decide
    · apply IsUnit.of_mul_eq_one (1879 : ZMod 8081)
      decide
    · apply IsUnit.of_mul_eq_one (4940 : ZMod 8081)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8087 : Nat.Prime 8087 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8087 8086 1 5 [2, 13, 311]
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
    · apply IsUnit.of_mul_eq_one (4043 : ZMod 8087)
      decide
    · apply IsUnit.of_mul_eq_one (1618 : ZMod 8087)
      decide
    · apply IsUnit.of_mul_eq_one (2827 : ZMod 8087)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8089 : Nat.Prime 8089 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8089 8088 1 17 [2, 2, 2, 3, 337]
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
    · apply IsUnit.of_mul_eq_one (4044 : ZMod 8089)
      decide
    · apply IsUnit.of_mul_eq_one (3167 : ZMod 8089)
      decide
    · apply IsUnit.of_mul_eq_one (2666 : ZMod 8089)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8093 : Nat.Prime 8093 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8093 8092 1 2 [2, 2, 7, 17, 17]
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
    · apply IsUnit.of_mul_eq_one (4046 : ZMod 8093)
      decide
    · apply IsUnit.of_mul_eq_one (636 : ZMod 8093)
      decide
    · apply IsUnit.of_mul_eq_one (4863 : ZMod 8093)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8101 : Nat.Prime 8101 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8101 8100 1 6 [2, 2, 3, 3, 3, 3, 5, 5]
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
    · apply IsUnit.of_mul_eq_one (4050 : ZMod 8101)
      decide
    · apply IsUnit.of_mul_eq_one (3439 : ZMod 8101)
      decide
    · apply IsUnit.of_mul_eq_one (2794 : ZMod 8101)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 8039) (q := 8053) (by exact lowPrime_8053) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8053) (q := 8059) (by exact lowPrime_8059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8059) (q := 8069) (by exact lowPrime_8069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8069) (q := 8081) (by exact lowPrime_8081) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8081) (q := 8087) (by exact lowPrime_8087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8087) (q := 8089) (by exact lowPrime_8089) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8089) (q := 8093) (by exact lowPrime_8093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8093) (q := 8101) (by exact lowPrime_8101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part05_chain :
    DusartPrimeRowsChain 8039 8100 dusartPrimeRows_7717_8110_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]
