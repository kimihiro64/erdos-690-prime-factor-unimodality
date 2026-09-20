import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 177 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_15241 : Nat.Prime 15241 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15241 15240 1 11 [2, 2, 2, 3, 5, 127]
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
    · change IsUnit ((11 : ZMod 15241) ^ 7620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7620 : ZMod 15241)
      decide
    · change IsUnit ((11 : ZMod 15241) ^ 7620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7620 : ZMod 15241)
      decide
    · change IsUnit ((11 : ZMod 15241) ^ 7620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7620 : ZMod 15241)
      decide
    · change IsUnit ((11 : ZMod 15241) ^ 5080 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8031 : ZMod 15241)
      decide
    · change IsUnit ((11 : ZMod 15241) ^ 3048 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11917 : ZMod 15241)
      decide
    · change IsUnit ((11 : ZMod 15241) ^ 120 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14000 : ZMod 15241)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15259 : Nat.Prime 15259 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15259 15258 1 2 [2, 3, 2543]
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
    · change IsUnit ((2 : ZMod 15259) ^ 7629 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7629 : ZMod 15259)
      decide
    · change IsUnit ((2 : ZMod 15259) ^ 5086 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8463 : ZMod 15259)
      decide
    · change IsUnit ((2 : ZMod 15259) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7024 : ZMod 15259)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15263 : Nat.Prime 15263 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15263 15262 1 5 [2, 13, 587]
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
    · change IsUnit ((5 : ZMod 15263) ^ 7631 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7631 : ZMod 15263)
      decide
    · change IsUnit ((5 : ZMod 15263) ^ 1174 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12773 : ZMod 15263)
      decide
    · change IsUnit ((5 : ZMod 15263) ^ 26 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2628 : ZMod 15263)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15269 : Nat.Prime 15269 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15269 15268 1 2 [2, 2, 11, 347]
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
    · change IsUnit ((2 : ZMod 15269) ^ 7634 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7634 : ZMod 15269)
      decide
    · change IsUnit ((2 : ZMod 15269) ^ 7634 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7634 : ZMod 15269)
      decide
    · change IsUnit ((2 : ZMod 15269) ^ 1388 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13311 : ZMod 15269)
      decide
    · change IsUnit ((2 : ZMod 15269) ^ 44 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10324 : ZMod 15269)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15271 : Nat.Prime 15271 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15271 15270 1 11 [2, 3, 5, 509]
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
    · change IsUnit ((11 : ZMod 15271) ^ 7635 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7635 : ZMod 15271)
      decide
    · change IsUnit ((11 : ZMod 15271) ^ 5090 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4080 : ZMod 15271)
      decide
    · change IsUnit ((11 : ZMod 15271) ^ 3054 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1964 : ZMod 15271)
      decide
    · change IsUnit ((11 : ZMod 15271) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2101 : ZMod 15271)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15277 : Nat.Prime 15277 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15277 15276 1 6 [2, 2, 3, 19, 67]
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
    · change IsUnit ((6 : ZMod 15277) ^ 7638 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7638 : ZMod 15277)
      decide
    · change IsUnit ((6 : ZMod 15277) ^ 7638 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7638 : ZMod 15277)
      decide
    · change IsUnit ((6 : ZMod 15277) ^ 5092 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5362 : ZMod 15277)
      decide
    · change IsUnit ((6 : ZMod 15277) ^ 804 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8071 : ZMod 15277)
      decide
    · change IsUnit ((6 : ZMod 15277) ^ 228 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3265 : ZMod 15277)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15287 : Nat.Prime 15287 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15287 15286 1 5 [2, 7643]
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
    · change IsUnit ((5 : ZMod 15287) ^ 7643 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7643 : ZMod 15287)
      decide
    · change IsUnit ((5 : ZMod 15287) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (637 : ZMod 15287)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15289 : Nat.Prime 15289 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15289 15288 1 11 [2, 2, 2, 3, 7, 7, 13]
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
    · change IsUnit ((11 : ZMod 15289) ^ 7644 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7644 : ZMod 15289)
      decide
    · change IsUnit ((11 : ZMod 15289) ^ 7644 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7644 : ZMod 15289)
      decide
    · change IsUnit ((11 : ZMod 15289) ^ 7644 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7644 : ZMod 15289)
      decide
    · change IsUnit ((11 : ZMod 15289) ^ 5096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5818 : ZMod 15289)
      decide
    · change IsUnit ((11 : ZMod 15289) ^ 2184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8016 : ZMod 15289)
      decide
    · change IsUnit ((11 : ZMod 15289) ^ 2184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8016 : ZMod 15289)
      decide
    · change IsUnit ((11 : ZMod 15289) ^ 1176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10824 : ZMod 15289)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15233) (q := 15241) (by exact lowPrime_15241) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15241) (q := 15259) (by exact lowPrime_15259) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15259) (q := 15263) (by exact lowPrime_15263) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15263) (q := 15269) (by exact lowPrime_15269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15269) (q := 15271) (by exact lowPrime_15271) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15271) (q := 15277) (by exact lowPrime_15277) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15277) (q := 15287) (by exact lowPrime_15287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15287) (q := 15289) (by exact lowPrime_15289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part07_chain :
    DusartPrimeRowsChain 15233 15289 dusartPrimeRows_14767_15526_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · apply DusartPrimeRowsChain.empty
                  norm_num
