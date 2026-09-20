import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 13 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4013 : Nat.Prime 4013 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4013 4012 1 2 [2, 2, 17, 59]
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
    · apply IsUnit.of_mul_eq_one (2006 : ZMod 4013)
      decide
    · apply IsUnit.of_mul_eq_one (1824 : ZMod 4013)
      decide
    · apply IsUnit.of_mul_eq_one (1179 : ZMod 4013)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4019 : Nat.Prime 4019 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4019 4018 1 2 [2, 7, 7, 41]
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
    · apply IsUnit.of_mul_eq_one (2009 : ZMod 4019)
      decide
    · apply IsUnit.of_mul_eq_one (2438 : ZMod 4019)
      decide
    · apply IsUnit.of_mul_eq_one (3026 : ZMod 4019)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4021 : Nat.Prime 4021 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4021 4020 1 2 [2, 2, 3, 5, 67]
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
    · apply IsUnit.of_mul_eq_one (2010 : ZMod 4021)
      decide
    · apply IsUnit.of_mul_eq_one (1944 : ZMod 4021)
      decide
    · apply IsUnit.of_mul_eq_one (1527 : ZMod 4021)
      decide
    · apply IsUnit.of_mul_eq_one (3694 : ZMod 4021)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4027 : Nat.Prime 4027 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4027 4026 1 3 [2, 3, 11, 61]
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
    · apply IsUnit.of_mul_eq_one (2013 : ZMod 4027)
      decide
    · apply IsUnit.of_mul_eq_one (3291 : ZMod 4027)
      decide
    · apply IsUnit.of_mul_eq_one (3139 : ZMod 4027)
      decide
    · apply IsUnit.of_mul_eq_one (1678 : ZMod 4027)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4049 : Nat.Prime 4049 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4049 4048 1 3 [2, 2, 2, 2, 11, 23]
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
    · apply IsUnit.of_mul_eq_one (2024 : ZMod 4049)
      decide
    · apply IsUnit.of_mul_eq_one (749 : ZMod 4049)
      decide
    · apply IsUnit.of_mul_eq_one (3208 : ZMod 4049)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4051 : Nat.Prime 4051 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4051 4050 1 10 [2, 3, 3, 3, 3, 5, 5]
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
    · apply IsUnit.of_mul_eq_one (2025 : ZMod 4051)
      decide
    · apply IsUnit.of_mul_eq_one (1084 : ZMod 4051)
      decide
    · apply IsUnit.of_mul_eq_one (491 : ZMod 4051)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4057 : Nat.Prime 4057 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4057 4056 1 5 [2, 2, 2, 3, 13, 13]
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
    · apply IsUnit.of_mul_eq_one (2028 : ZMod 4057)
      decide
    · apply IsUnit.of_mul_eq_one (469 : ZMod 4057)
      decide
    · apply IsUnit.of_mul_eq_one (1621 : ZMod 4057)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4073 : Nat.Prime 4073 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4073 4072 1 3 [2, 2, 2, 509]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (2036 : ZMod 4073)
      decide
    · apply IsUnit.of_mul_eq_one (660 : ZMod 4073)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4007) (q := 4013) (by exact lowPrime_4013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4013) (q := 4019) (by exact lowPrime_4019) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4019) (q := 4021) (by exact lowPrime_4021) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4021) (q := 4027) (by exact lowPrime_4027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4027) (q := 4049) (by exact lowPrime_4049) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4049) (q := 4051) (by exact lowPrime_4051) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4051) (q := 4057) (by exact lowPrime_4057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4057) (q := 4073) (by exact lowPrime_4073) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part04_chain :
    DusartPrimeRowsChain 4007 4072 dusartPrimeRows_3803_4672_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]
