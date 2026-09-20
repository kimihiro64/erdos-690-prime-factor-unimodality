import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 05 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_3539 : Nat.Prime 3539 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3539 3538 1 2 [2, 29, 61]
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
    · change IsUnit ((2 : ZMod 3539) ^ 1769 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1769 : ZMod 3539)
      decide
    · change IsUnit ((2 : ZMod 3539) ^ 122 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1358 : ZMod 3539)
      decide
    · change IsUnit ((2 : ZMod 3539) ^ 58 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (752 : ZMod 3539)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3541 : Nat.Prime 3541 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3541 3540 1 7 [2, 2, 3, 5, 59]
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
    · change IsUnit ((7 : ZMod 3541) ^ 1770 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1770 : ZMod 3541)
      decide
    · change IsUnit ((7 : ZMod 3541) ^ 1770 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1770 : ZMod 3541)
      decide
    · change IsUnit ((7 : ZMod 3541) ^ 1180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1160 : ZMod 3541)
      decide
    · change IsUnit ((7 : ZMod 3541) ^ 708 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2944 : ZMod 3541)
      decide
    · change IsUnit ((7 : ZMod 3541) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1894 : ZMod 3541)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3547 : Nat.Prime 3547 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3547 3546 1 2 [2, 3, 3, 197]
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
    · change IsUnit ((2 : ZMod 3547) ^ 1773 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1773 : ZMod 3547)
      decide
    · change IsUnit ((2 : ZMod 3547) ^ 1182 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (387 : ZMod 3547)
      decide
    · change IsUnit ((2 : ZMod 3547) ^ 1182 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (387 : ZMod 3547)
      decide
    · change IsUnit ((2 : ZMod 3547) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3367 : ZMod 3547)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3557 : Nat.Prime 3557 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3557 3556 1 2 [2, 2, 7, 127]
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
    · change IsUnit ((2 : ZMod 3557) ^ 1778 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1778 : ZMod 3557)
      decide
    · change IsUnit ((2 : ZMod 3557) ^ 1778 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1778 : ZMod 3557)
      decide
    · change IsUnit ((2 : ZMod 3557) ^ 508 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1143 : ZMod 3557)
      decide
    · change IsUnit ((2 : ZMod 3557) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1741 : ZMod 3557)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3559 : Nat.Prime 3559 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3559 3558 1 3 [2, 3, 593]
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
    · change IsUnit ((3 : ZMod 3559) ^ 1779 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1779 : ZMod 3559)
      decide
    · change IsUnit ((3 : ZMod 3559) ^ 1186 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (478 : ZMod 3559)
      decide
    · change IsUnit ((3 : ZMod 3559) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (44 : ZMod 3559)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3571 : Nat.Prime 3571 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3571 3570 1 2 [2, 3, 5, 7, 17]
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
    · change IsUnit ((2 : ZMod 3571) ^ 1785 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1785 : ZMod 3571)
      decide
    · change IsUnit ((2 : ZMod 3571) ^ 1190 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (34 : ZMod 3571)
      decide
    · change IsUnit ((2 : ZMod 3571) ^ 714 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2066 : ZMod 3571)
      decide
    · change IsUnit ((2 : ZMod 3571) ^ 510 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (936 : ZMod 3571)
      decide
    · change IsUnit ((2 : ZMod 3571) ^ 210 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1151 : ZMod 3571)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3581 : Nat.Prime 3581 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3581 3580 1 2 [2, 2, 5, 179]
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
    · change IsUnit ((2 : ZMod 3581) ^ 1790 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1790 : ZMod 3581)
      decide
    · change IsUnit ((2 : ZMod 3581) ^ 1790 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1790 : ZMod 3581)
      decide
    · change IsUnit ((2 : ZMod 3581) ^ 716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1290 : ZMod 3581)
      decide
    · change IsUnit ((2 : ZMod 3581) ^ 20 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1649 : ZMod 3581)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3583 : Nat.Prime 3583 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3583 3582 1 3 [2, 3, 3, 199]
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
    · change IsUnit ((3 : ZMod 3583) ^ 1791 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1791 : ZMod 3583)
      decide
    · change IsUnit ((3 : ZMod 3583) ^ 1194 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2042 : ZMod 3583)
      decide
    · change IsUnit ((3 : ZMod 3583) ^ 1194 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2042 : ZMod 3583)
      decide
    · change IsUnit ((3 : ZMod 3583) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (52 : ZMod 3583)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3533) (q := 3539) (by exact lowPrime_3539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3539) (q := 3541) (by exact lowPrime_3541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3541) (q := 3547) (by exact lowPrime_3547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3547) (q := 3557) (by exact lowPrime_3557) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3557) (q := 3559) (by exact lowPrime_3559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3559) (q := 3571) (by exact lowPrime_3571) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3571) (q := 3581) (by exact lowPrime_3581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3581) (q := 3583) (by exact lowPrime_3583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part05_chain :
    DusartPrimeRowsChain 3533 3583 dusartPrimeRows_3275_3802_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num
