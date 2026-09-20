import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 190 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_16127 : Nat.Prime 16127 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16127 16126 1 5 [2, 11, 733]
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
    · change IsUnit ((5 : ZMod 16127) ^ 8063 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8063 : ZMod 16127)
      decide
    · change IsUnit ((5 : ZMod 16127) ^ 1466 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13280 : ZMod 16127)
      decide
    · change IsUnit ((5 : ZMod 16127) ^ 22 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14734 : ZMod 16127)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16139 : Nat.Prime 16139 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16139 16138 1 2 [2, 8069]
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
    · change IsUnit ((2 : ZMod 16139) ^ 8069 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8069 : ZMod 16139)
      decide
    · change IsUnit ((2 : ZMod 16139) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5380 : ZMod 16139)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16141 : Nat.Prime 16141 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16141 16140 1 6 [2, 2, 3, 5, 269]
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
    · change IsUnit ((6 : ZMod 16141) ^ 8070 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8070 : ZMod 16141)
      decide
    · change IsUnit ((6 : ZMod 16141) ^ 8070 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8070 : ZMod 16141)
      decide
    · change IsUnit ((6 : ZMod 16141) ^ 5380 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14806 : ZMod 16141)
      decide
    · change IsUnit ((6 : ZMod 16141) ^ 3228 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5663 : ZMod 16141)
      decide
    · change IsUnit ((6 : ZMod 16141) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10953 : ZMod 16141)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16183 : Nat.Prime 16183 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16183 16182 1 3 [2, 3, 3, 29, 31]
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
    · change IsUnit ((3 : ZMod 16183) ^ 8091 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8091 : ZMod 16183)
      decide
    · change IsUnit ((3 : ZMod 16183) ^ 5394 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1736 : ZMod 16183)
      decide
    · change IsUnit ((3 : ZMod 16183) ^ 5394 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1736 : ZMod 16183)
      decide
    · change IsUnit ((3 : ZMod 16183) ^ 558 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13883 : ZMod 16183)
      decide
    · change IsUnit ((3 : ZMod 16183) ^ 522 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10512 : ZMod 16183)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16187 : Nat.Prime 16187 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16187 16186 1 2 [2, 8093]
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
    · change IsUnit ((2 : ZMod 16187) ^ 8093 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8093 : ZMod 16187)
      decide
    · change IsUnit ((2 : ZMod 16187) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5396 : ZMod 16187)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16189 : Nat.Prime 16189 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16189 16188 1 2 [2, 2, 3, 19, 71]
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
    · change IsUnit ((2 : ZMod 16189) ^ 8094 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8094 : ZMod 16189)
      decide
    · change IsUnit ((2 : ZMod 16189) ^ 8094 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8094 : ZMod 16189)
      decide
    · change IsUnit ((2 : ZMod 16189) ^ 5396 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1972 : ZMod 16189)
      decide
    · change IsUnit ((2 : ZMod 16189) ^ 852 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2237 : ZMod 16189)
      decide
    · change IsUnit ((2 : ZMod 16189) ^ 228 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15594 : ZMod 16189)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16193 : Nat.Prime 16193 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16193 16192 1 5 [2, 2, 2, 2, 2, 2, 11, 23]
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
    · change IsUnit ((5 : ZMod 16193) ^ 8096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8096 : ZMod 16193)
      decide
    · change IsUnit ((5 : ZMod 16193) ^ 8096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8096 : ZMod 16193)
      decide
    · change IsUnit ((5 : ZMod 16193) ^ 8096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8096 : ZMod 16193)
      decide
    · change IsUnit ((5 : ZMod 16193) ^ 8096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8096 : ZMod 16193)
      decide
    · change IsUnit ((5 : ZMod 16193) ^ 8096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8096 : ZMod 16193)
      decide
    · change IsUnit ((5 : ZMod 16193) ^ 8096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8096 : ZMod 16193)
      decide
    · change IsUnit ((5 : ZMod 16193) ^ 1472 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6866 : ZMod 16193)
      decide
    · change IsUnit ((5 : ZMod 16193) ^ 704 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3036 : ZMod 16193)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16217 : Nat.Prime 16217 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16217 16216 1 3 [2, 2, 2, 2027]
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
    · change IsUnit ((3 : ZMod 16217) ^ 8108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8108 : ZMod 16217)
      decide
    · change IsUnit ((3 : ZMod 16217) ^ 8108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8108 : ZMod 16217)
      decide
    · change IsUnit ((3 : ZMod 16217) ^ 8108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8108 : ZMod 16217)
      decide
    · change IsUnit ((3 : ZMod 16217) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15641 : ZMod 16217)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 16111) (q := 16127) (by exact lowPrime_16127) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16127) (q := 16139) (by exact lowPrime_16139) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16139) (q := 16141) (by exact lowPrime_16141) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16141) (q := 16183) (by exact lowPrime_16183) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16183) (q := 16187) (by exact lowPrime_16187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16187) (q := 16189) (by exact lowPrime_16189) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16189) (q := 16193) (by exact lowPrime_16193) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16193) (q := 16217) (by exact lowPrime_16217) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part09_chain :
    DusartPrimeRowsChain 16111 16217 dusartPrimeRows_15527_16318_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · apply DusartPrimeRowsChain.empty
                  norm_num
