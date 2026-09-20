import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 212 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_22669 : Nat.Prime 22669 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22669 22668 1 2 [2, 2, 3, 1889]
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
    · change IsUnit ((2 : ZMod 22669) ^ 11334 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11334 : ZMod 22669)
      decide
    · change IsUnit ((2 : ZMod 22669) ^ 11334 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11334 : ZMod 22669)
      decide
    · change IsUnit ((2 : ZMod 22669) ^ 7556 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19656 : ZMod 22669)
      decide
    · change IsUnit ((2 : ZMod 22669) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16170 : ZMod 22669)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22679 : Nat.Prime 22679 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22679 22678 1 13 [2, 17, 23, 29]
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
    · change IsUnit ((13 : ZMod 22679) ^ 11339 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11339 : ZMod 22679)
      decide
    · change IsUnit ((13 : ZMod 22679) ^ 1334 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13971 : ZMod 22679)
      decide
    · change IsUnit ((13 : ZMod 22679) ^ 986 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11157 : ZMod 22679)
      decide
    · change IsUnit ((13 : ZMod 22679) ^ 782 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (20717 : ZMod 22679)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22691 : Nat.Prime 22691 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22691 22690 1 2 [2, 5, 2269]
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
    · change IsUnit ((2 : ZMod 22691) ^ 11345 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11345 : ZMod 22691)
      decide
    · change IsUnit ((2 : ZMod 22691) ^ 4538 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4024 : ZMod 22691)
      decide
    · change IsUnit ((2 : ZMod 22691) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2085 : ZMod 22691)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22697 : Nat.Prime 22697 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22697 22696 1 3 [2, 2, 2, 2837]
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
    · change IsUnit ((3 : ZMod 22697) ^ 11348 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11348 : ZMod 22697)
      decide
    · change IsUnit ((3 : ZMod 22697) ^ 11348 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11348 : ZMod 22697)
      decide
    · change IsUnit ((3 : ZMod 22697) ^ 11348 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11348 : ZMod 22697)
      decide
    · change IsUnit ((3 : ZMod 22697) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8328 : ZMod 22697)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22699 : Nat.Prime 22699 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22699 22698 1 12 [2, 3, 3, 13, 97]
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
    · change IsUnit ((12 : ZMod 22699) ^ 11349 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11349 : ZMod 22699)
      decide
    · change IsUnit ((12 : ZMod 22699) ^ 7566 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10993 : ZMod 22699)
      decide
    · change IsUnit ((12 : ZMod 22699) ^ 7566 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10993 : ZMod 22699)
      decide
    · change IsUnit ((12 : ZMod 22699) ^ 1746 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1796 : ZMod 22699)
      decide
    · change IsUnit ((12 : ZMod 22699) ^ 234 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10634 : ZMod 22699)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22709 : Nat.Prime 22709 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22709 22708 1 2 [2, 2, 7, 811]
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
    · change IsUnit ((2 : ZMod 22709) ^ 11354 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11354 : ZMod 22709)
      decide
    · change IsUnit ((2 : ZMod 22709) ^ 11354 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11354 : ZMod 22709)
      decide
    · change IsUnit ((2 : ZMod 22709) ^ 3244 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (20398 : ZMod 22709)
      decide
    · change IsUnit ((2 : ZMod 22709) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10825 : ZMod 22709)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22717 : Nat.Prime 22717 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22717 22716 1 2 [2, 2, 3, 3, 631]
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
    · change IsUnit ((2 : ZMod 22717) ^ 11358 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11358 : ZMod 22717)
      decide
    · change IsUnit ((2 : ZMod 22717) ^ 11358 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11358 : ZMod 22717)
      decide
    · change IsUnit ((2 : ZMod 22717) ^ 7572 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18270 : ZMod 22717)
      decide
    · change IsUnit ((2 : ZMod 22717) ^ 7572 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18270 : ZMod 22717)
      decide
    · change IsUnit ((2 : ZMod 22717) ^ 36 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9265 : ZMod 22717)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22721 : Nat.Prime 22721 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22721 22720 1 3 [2, 2, 2, 2, 2, 2, 5, 71]
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
    · change IsUnit ((3 : ZMod 22721) ^ 11360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11360 : ZMod 22721)
      decide
    · change IsUnit ((3 : ZMod 22721) ^ 11360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11360 : ZMod 22721)
      decide
    · change IsUnit ((3 : ZMod 22721) ^ 11360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11360 : ZMod 22721)
      decide
    · change IsUnit ((3 : ZMod 22721) ^ 11360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11360 : ZMod 22721)
      decide
    · change IsUnit ((3 : ZMod 22721) ^ 11360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11360 : ZMod 22721)
      decide
    · change IsUnit ((3 : ZMod 22721) ^ 11360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11360 : ZMod 22721)
      decide
    · change IsUnit ((3 : ZMod 22721) ^ 4544 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3097 : ZMod 22721)
      decide
    · change IsUnit ((3 : ZMod 22721) ^ 320 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12059 : ZMod 22721)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22651) (q := 22669) (by exact lowPrime_22669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22669) (q := 22679) (by exact lowPrime_22679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22679) (q := 22691) (by exact lowPrime_22691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22691) (q := 22697) (by exact lowPrime_22697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22697) (q := 22699) (by exact lowPrime_22699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22699) (q := 22709) (by exact lowPrime_22709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22709) (q := 22717) (by exact lowPrime_22717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22717) (q := 22721) (by exact lowPrime_22721) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part09_chain :
    DusartPrimeRowsChain 22651 22721 dusartPrimeRows_22027_23158_part09 := by
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
