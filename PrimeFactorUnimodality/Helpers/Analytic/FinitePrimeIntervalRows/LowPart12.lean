import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 12 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_3931 : Nat.Prime 3931 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3931 3930 1 2 [2, 3, 5, 131]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 3931) ^ 1965 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1965 : ZMod 3931)
      decide
    · change IsUnit ((2 : ZMod 3931) ^ 1310 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2826 : ZMod 3931)
      decide
    · change IsUnit ((2 : ZMod 3931) ^ 786 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2173 : ZMod 3931)
      decide
    · change IsUnit ((2 : ZMod 3931) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (704 : ZMod 3931)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3943 : Nat.Prime 3943 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3943 3942 1 3 [2, 3, 3, 3, 73]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 3943) ^ 1971 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1971 : ZMod 3943)
      decide
    · change IsUnit ((3 : ZMod 3943) ^ 1314 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3564 : ZMod 3943)
      decide
    · change IsUnit ((3 : ZMod 3943) ^ 1314 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3564 : ZMod 3943)
      decide
    · change IsUnit ((3 : ZMod 3943) ^ 1314 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3564 : ZMod 3943)
      decide
    · change IsUnit ((3 : ZMod 3943) ^ 54 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2318 : ZMod 3943)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3947 : Nat.Prime 3947 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3947 3946 1 2 [2, 1973]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · change IsUnit ((2 : ZMod 3947) ^ 1973 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1973 : ZMod 3947)
      decide
    · change IsUnit ((2 : ZMod 3947) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1316 : ZMod 3947)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3967 : Nat.Prime 3967 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3967 3966 1 6 [2, 3, 661]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((6 : ZMod 3967) ^ 1983 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1983 : ZMod 3967)
      decide
    · change IsUnit ((6 : ZMod 3967) ^ 1322 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2348 : ZMod 3967)
      decide
    · change IsUnit ((6 : ZMod 3967) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (464 : ZMod 3967)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3989 : Nat.Prime 3989 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3989 3988 1 2 [2, 2, 997]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 3989) ^ 1994 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1994 : ZMod 3989)
      decide
    · change IsUnit ((2 : ZMod 3989) ^ 1994 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1994 : ZMod 3989)
      decide
    · change IsUnit ((2 : ZMod 3989) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (266 : ZMod 3989)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4001 : Nat.Prime 4001 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4001 4000 1 3 [2, 2, 2, 2, 2, 5, 5, 5]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 4001) ^ 2000 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2000 : ZMod 4001)
      decide
    · change IsUnit ((3 : ZMod 4001) ^ 2000 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2000 : ZMod 4001)
      decide
    · change IsUnit ((3 : ZMod 4001) ^ 2000 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2000 : ZMod 4001)
      decide
    · change IsUnit ((3 : ZMod 4001) ^ 2000 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2000 : ZMod 4001)
      decide
    · change IsUnit ((3 : ZMod 4001) ^ 2000 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2000 : ZMod 4001)
      decide
    · change IsUnit ((3 : ZMod 4001) ^ 800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2855 : ZMod 4001)
      decide
    · change IsUnit ((3 : ZMod 4001) ^ 800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2855 : ZMod 4001)
      decide
    · change IsUnit ((3 : ZMod 4001) ^ 800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2855 : ZMod 4001)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4003 : Nat.Prime 4003 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4003 4002 1 2 [2, 3, 23, 29]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 4003) ^ 2001 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2001 : ZMod 4003)
      decide
    · change IsUnit ((2 : ZMod 4003) ^ 1334 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2394 : ZMod 4003)
      decide
    · change IsUnit ((2 : ZMod 4003) ^ 174 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1961 : ZMod 4003)
      decide
    · change IsUnit ((2 : ZMod 4003) ^ 138 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1192 : ZMod 4003)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4007 : Nat.Prime 4007 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4007 4006 1 5 [2, 2003]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · change IsUnit ((5 : ZMod 4007) ^ 2003 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2003 : ZMod 4007)
      decide
    · change IsUnit ((5 : ZMod 4007) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (167 : ZMod 4007)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3929) (q := 3931) (by exact lowPrime_3931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3931) (q := 3943) (by exact lowPrime_3943) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3943) (q := 3947) (by exact lowPrime_3947) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3947) (q := 3967) (by exact lowPrime_3967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3967) (q := 3989) (by exact lowPrime_3989) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3989) (q := 4001) (by exact lowPrime_4001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4001) (q := 4003) (by exact lowPrime_4003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4003) (q := 4007) (by exact lowPrime_4007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part03_chain :
    DusartPrimeRowsChain 3929 4007 dusartPrimeRows_3803_4672_part03 := by
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
                  norm_num
