import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 81 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_8423 : Nat.Prime 8423 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8423 8422 1 5 [2, 4211]
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
    · change IsUnit ((5 : ZMod 8423) ^ 4211 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4211 : ZMod 8423)
      decide
    · change IsUnit ((5 : ZMod 8423) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (351 : ZMod 8423)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8429 : Nat.Prime 8429 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8429 8428 1 2 [2, 2, 7, 7, 43]
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
    · change IsUnit ((2 : ZMod 8429) ^ 4214 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4214 : ZMod 8429)
      decide
    · change IsUnit ((2 : ZMod 8429) ^ 4214 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4214 : ZMod 8429)
      decide
    · change IsUnit ((2 : ZMod 8429) ^ 1204 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5886 : ZMod 8429)
      decide
    · change IsUnit ((2 : ZMod 8429) ^ 1204 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5886 : ZMod 8429)
      decide
    · change IsUnit ((2 : ZMod 8429) ^ 196 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6920 : ZMod 8429)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8431 : Nat.Prime 8431 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8431 8430 1 3 [2, 3, 5, 281]
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
    · change IsUnit ((3 : ZMod 8431) ^ 4215 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4215 : ZMod 8431)
      decide
    · change IsUnit ((3 : ZMod 8431) ^ 2810 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6336 : ZMod 8431)
      decide
    · change IsUnit ((3 : ZMod 8431) ^ 1686 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (876 : ZMod 8431)
      decide
    · change IsUnit ((3 : ZMod 8431) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1436 : ZMod 8431)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8443 : Nat.Prime 8443 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8443 8442 1 2 [2, 3, 3, 7, 67]
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
    · change IsUnit ((2 : ZMod 8443) ^ 4221 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4221 : ZMod 8443)
      decide
    · change IsUnit ((2 : ZMod 8443) ^ 2814 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5283 : ZMod 8443)
      decide
    · change IsUnit ((2 : ZMod 8443) ^ 2814 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5283 : ZMod 8443)
      decide
    · change IsUnit ((2 : ZMod 8443) ^ 1206 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1903 : ZMod 8443)
      decide
    · change IsUnit ((2 : ZMod 8443) ^ 126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6328 : ZMod 8443)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8447 : Nat.Prime 8447 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8447 8446 1 5 [2, 41, 103]
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
    · change IsUnit ((5 : ZMod 8447) ^ 4223 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4223 : ZMod 8447)
      decide
    · change IsUnit ((5 : ZMod 8447) ^ 206 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2321 : ZMod 8447)
      decide
    · change IsUnit ((5 : ZMod 8447) ^ 82 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8260 : ZMod 8447)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8461 : Nat.Prime 8461 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8461 8460 1 6 [2, 2, 3, 3, 5, 47]
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
    · change IsUnit ((6 : ZMod 8461) ^ 4230 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4230 : ZMod 8461)
      decide
    · change IsUnit ((6 : ZMod 8461) ^ 4230 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4230 : ZMod 8461)
      decide
    · change IsUnit ((6 : ZMod 8461) ^ 2820 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3412 : ZMod 8461)
      decide
    · change IsUnit ((6 : ZMod 8461) ^ 2820 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3412 : ZMod 8461)
      decide
    · change IsUnit ((6 : ZMod 8461) ^ 1692 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5189 : ZMod 8461)
      decide
    · change IsUnit ((6 : ZMod 8461) ^ 180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7446 : ZMod 8461)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8467 : Nat.Prime 8467 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8467 8466 1 2 [2, 3, 17, 83]
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
    · change IsUnit ((2 : ZMod 8467) ^ 4233 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4233 : ZMod 8467)
      decide
    · change IsUnit ((2 : ZMod 8467) ^ 2822 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7040 : ZMod 8467)
      decide
    · change IsUnit ((2 : ZMod 8467) ^ 498 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4751 : ZMod 8467)
      decide
    · change IsUnit ((2 : ZMod 8467) ^ 102 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5649 : ZMod 8467)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8501 : Nat.Prime 8501 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8501 8500 1 7 [2, 2, 5, 5, 5, 17]
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
    · change IsUnit ((7 : ZMod 8501) ^ 4250 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4250 : ZMod 8501)
      decide
    · change IsUnit ((7 : ZMod 8501) ^ 4250 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4250 : ZMod 8501)
      decide
    · change IsUnit ((7 : ZMod 8501) ^ 1700 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1505 : ZMod 8501)
      decide
    · change IsUnit ((7 : ZMod 8501) ^ 1700 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1505 : ZMod 8501)
      decide
    · change IsUnit ((7 : ZMod 8501) ^ 1700 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1505 : ZMod 8501)
      decide
    · change IsUnit ((7 : ZMod 8501) ^ 500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (789 : ZMod 8501)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8419) (q := 8423) (by exact lowPrime_8423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8423) (q := 8429) (by exact lowPrime_8429) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8429) (q := 8431) (by exact lowPrime_8431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8431) (q := 8443) (by exact lowPrime_8443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8443) (q := 8447) (by exact lowPrime_8447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8447) (q := 8461) (by exact lowPrime_8461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8461) (q := 8467) (by exact lowPrime_8467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8467) (q := 8501) (by exact lowPrime_8501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part05_chain :
    DusartPrimeRowsChain 8419 8501 dusartPrimeRows_8111_8520_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num
