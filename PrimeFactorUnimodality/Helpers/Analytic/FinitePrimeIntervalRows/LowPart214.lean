import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 214 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_22807 : Nat.Prime 22807 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22807 22806 1 3 [2, 3, 3, 7, 181]
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
    · change IsUnit ((3 : ZMod 22807) ^ 11403 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11403 : ZMod 22807)
      decide
    · change IsUnit ((3 : ZMod 22807) ^ 7602 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12539 : ZMod 22807)
      decide
    · change IsUnit ((3 : ZMod 22807) ^ 7602 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12539 : ZMod 22807)
      decide
    · change IsUnit ((3 : ZMod 22807) ^ 3258 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16923 : ZMod 22807)
      decide
    · change IsUnit ((3 : ZMod 22807) ^ 126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14424 : ZMod 22807)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22811 : Nat.Prime 22811 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22811 22810 1 6 [2, 5, 2281]
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
    · change IsUnit ((6 : ZMod 22811) ^ 11405 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11405 : ZMod 22811)
      decide
    · change IsUnit ((6 : ZMod 22811) ^ 4562 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12253 : ZMod 22811)
      decide
    · change IsUnit ((6 : ZMod 22811) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (548 : ZMod 22811)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22817 : Nat.Prime 22817 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22817 22816 1 3 [2, 2, 2, 2, 2, 23, 31]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 22817) ^ 11408 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11408 : ZMod 22817)
      decide
    · change IsUnit ((3 : ZMod 22817) ^ 11408 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11408 : ZMod 22817)
      decide
    · change IsUnit ((3 : ZMod 22817) ^ 11408 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11408 : ZMod 22817)
      decide
    · change IsUnit ((3 : ZMod 22817) ^ 11408 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11408 : ZMod 22817)
      decide
    · change IsUnit ((3 : ZMod 22817) ^ 11408 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11408 : ZMod 22817)
      decide
    · change IsUnit ((3 : ZMod 22817) ^ 992 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7296 : ZMod 22817)
      decide
    · change IsUnit ((3 : ZMod 22817) ^ 736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13965 : ZMod 22817)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22853 : Nat.Prime 22853 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22853 22852 1 2 [2, 2, 29, 197]
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
    · change IsUnit ((2 : ZMod 22853) ^ 11426 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11426 : ZMod 22853)
      decide
    · change IsUnit ((2 : ZMod 22853) ^ 11426 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11426 : ZMod 22853)
      decide
    · change IsUnit ((2 : ZMod 22853) ^ 788 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5735 : ZMod 22853)
      decide
    · change IsUnit ((2 : ZMod 22853) ^ 116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14094 : ZMod 22853)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22859 : Nat.Prime 22859 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22859 22858 1 2 [2, 11, 1039]
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
    · change IsUnit ((2 : ZMod 22859) ^ 11429 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11429 : ZMod 22859)
      decide
    · change IsUnit ((2 : ZMod 22859) ^ 2078 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10199 : ZMod 22859)
      decide
    · change IsUnit ((2 : ZMod 22859) ^ 22 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13673 : ZMod 22859)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22861 : Nat.Prime 22861 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22861 22860 1 2 [2, 2, 3, 3, 5, 127]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 22861) ^ 11430 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11430 : ZMod 22861)
      decide
    · change IsUnit ((2 : ZMod 22861) ^ 11430 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11430 : ZMod 22861)
      decide
    · change IsUnit ((2 : ZMod 22861) ^ 7620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16488 : ZMod 22861)
      decide
    · change IsUnit ((2 : ZMod 22861) ^ 7620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16488 : ZMod 22861)
      decide
    · change IsUnit ((2 : ZMod 22861) ^ 4572 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13064 : ZMod 22861)
      decide
    · change IsUnit ((2 : ZMod 22861) ^ 180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9978 : ZMod 22861)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22871 : Nat.Prime 22871 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22871 22870 1 7 [2, 5, 2287]
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
    · change IsUnit ((7 : ZMod 22871) ^ 11435 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11435 : ZMod 22871)
      decide
    · change IsUnit ((7 : ZMod 22871) ^ 4574 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1417 : ZMod 22871)
      decide
    · change IsUnit ((7 : ZMod 22871) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1130 : ZMod 22871)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22877 : Nat.Prime 22877 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22877 22876 1 2 [2, 2, 7, 19, 43]
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
    · change IsUnit ((2 : ZMod 22877) ^ 11438 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11438 : ZMod 22877)
      decide
    · change IsUnit ((2 : ZMod 22877) ^ 11438 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11438 : ZMod 22877)
      decide
    · change IsUnit ((2 : ZMod 22877) ^ 3268 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (483 : ZMod 22877)
      decide
    · change IsUnit ((2 : ZMod 22877) ^ 1204 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (20321 : ZMod 22877)
      decide
    · change IsUnit ((2 : ZMod 22877) ^ 532 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9915 : ZMod 22877)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22787) (q := 22807) (by exact lowPrime_22807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22807) (q := 22811) (by exact lowPrime_22811) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22811) (q := 22817) (by exact lowPrime_22817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22817) (q := 22853) (by exact lowPrime_22853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22853) (q := 22859) (by exact lowPrime_22859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22859) (q := 22861) (by exact lowPrime_22861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22861) (q := 22871) (by exact lowPrime_22871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22871) (q := 22877) (by exact lowPrime_22877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part11_chain :
    DusartPrimeRowsChain 22787 22877 dusartPrimeRows_22027_23158_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num
