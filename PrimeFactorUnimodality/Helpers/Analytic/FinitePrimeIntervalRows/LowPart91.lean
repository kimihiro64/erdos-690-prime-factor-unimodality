import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 91 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_9041 : Nat.Prime 9041 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9041 9040 1 3 [2, 2, 2, 2, 5, 113]
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
    · change IsUnit ((3 : ZMod 9041) ^ 4520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4520 : ZMod 9041)
      decide
    · change IsUnit ((3 : ZMod 9041) ^ 4520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4520 : ZMod 9041)
      decide
    · change IsUnit ((3 : ZMod 9041) ^ 4520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4520 : ZMod 9041)
      decide
    · change IsUnit ((3 : ZMod 9041) ^ 4520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4520 : ZMod 9041)
      decide
    · change IsUnit ((3 : ZMod 9041) ^ 1808 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6185 : ZMod 9041)
      decide
    · change IsUnit ((3 : ZMod 9041) ^ 80 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2530 : ZMod 9041)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9043 : Nat.Prime 9043 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9043 9042 1 3 [2, 3, 11, 137]
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
    · change IsUnit ((3 : ZMod 9043) ^ 4521 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4521 : ZMod 9043)
      decide
    · change IsUnit ((3 : ZMod 9043) ^ 3014 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7079 : ZMod 9043)
      decide
    · change IsUnit ((3 : ZMod 9043) ^ 822 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2545 : ZMod 9043)
      decide
    · change IsUnit ((3 : ZMod 9043) ^ 66 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4942 : ZMod 9043)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9049 : Nat.Prime 9049 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9049 9048 1 7 [2, 2, 2, 3, 13, 29]
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
    · change IsUnit ((7 : ZMod 9049) ^ 4524 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4524 : ZMod 9049)
      decide
    · change IsUnit ((7 : ZMod 9049) ^ 4524 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4524 : ZMod 9049)
      decide
    · change IsUnit ((7 : ZMod 9049) ^ 4524 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4524 : ZMod 9049)
      decide
    · change IsUnit ((7 : ZMod 9049) ^ 3016 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2734 : ZMod 9049)
      decide
    · change IsUnit ((7 : ZMod 9049) ^ 696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8631 : ZMod 9049)
      decide
    · change IsUnit ((7 : ZMod 9049) ^ 312 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8210 : ZMod 9049)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9059 : Nat.Prime 9059 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9059 9058 1 2 [2, 7, 647]
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
    · change IsUnit ((2 : ZMod 9059) ^ 4529 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4529 : ZMod 9059)
      decide
    · change IsUnit ((2 : ZMod 9059) ^ 1294 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8032 : ZMod 9059)
      decide
    · change IsUnit ((2 : ZMod 9059) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3232 : ZMod 9059)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9067 : Nat.Prime 9067 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9067 9066 1 3 [2, 3, 1511]
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
    · change IsUnit ((3 : ZMod 9067) ^ 4533 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4533 : ZMod 9067)
      decide
    · change IsUnit ((3 : ZMod 9067) ^ 3022 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8706 : ZMod 9067)
      decide
    · change IsUnit ((3 : ZMod 9067) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8930 : ZMod 9067)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9091 : Nat.Prime 9091 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9091 9090 1 3 [2, 3, 3, 5, 101]
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
    · change IsUnit ((3 : ZMod 9091) ^ 4545 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4545 : ZMod 9091)
      decide
    · change IsUnit ((3 : ZMod 9091) ^ 3030 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1129 : ZMod 9091)
      decide
    · change IsUnit ((3 : ZMod 9091) ^ 3030 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1129 : ZMod 9091)
      decide
    · change IsUnit ((3 : ZMod 9091) ^ 1818 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3214 : ZMod 9091)
      decide
    · change IsUnit ((3 : ZMod 9091) ^ 90 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5371 : ZMod 9091)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9103 : Nat.Prime 9103 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9103 9102 1 6 [2, 3, 37, 41]
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
    · change IsUnit ((6 : ZMod 9103) ^ 4551 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4551 : ZMod 9103)
      decide
    · change IsUnit ((6 : ZMod 9103) ^ 3034 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1574 : ZMod 9103)
      decide
    · change IsUnit ((6 : ZMod 9103) ^ 246 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8168 : ZMod 9103)
      decide
    · change IsUnit ((6 : ZMod 9103) ^ 222 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7338 : ZMod 9103)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9109 : Nat.Prime 9109 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9109 9108 1 10 [2, 2, 3, 3, 11, 23]
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
    · change IsUnit ((10 : ZMod 9109) ^ 4554 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4554 : ZMod 9109)
      decide
    · change IsUnit ((10 : ZMod 9109) ^ 4554 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4554 : ZMod 9109)
      decide
    · change IsUnit ((10 : ZMod 9109) ^ 3036 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5032 : ZMod 9109)
      decide
    · change IsUnit ((10 : ZMod 9109) ^ 3036 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5032 : ZMod 9109)
      decide
    · change IsUnit ((10 : ZMod 9109) ^ 828 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2742 : ZMod 9109)
      decide
    · change IsUnit ((10 : ZMod 9109) ^ 396 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (975 : ZMod 9109)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9029) (q := 9041) (by exact lowPrime_9041) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9041) (q := 9043) (by exact lowPrime_9043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9043) (q := 9049) (by exact lowPrime_9049) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9049) (q := 9059) (by exact lowPrime_9059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9059) (q := 9067) (by exact lowPrime_9067) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9067) (q := 9091) (by exact lowPrime_9091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9091) (q := 9103) (by exact lowPrime_9103) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9103) (q := 9109) (by exact lowPrime_9109) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part02_chain :
    DusartPrimeRowsChain 9029 9109 dusartPrimeRows_8963_9418_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · apply DusartPrimeRowsChain.empty
                  norm_num
