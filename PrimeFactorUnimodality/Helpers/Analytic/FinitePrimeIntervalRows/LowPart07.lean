import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 07 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_3659 : Nat.Prime 3659 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3659 3658 1 2 [2, 31, 59]
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
    · change IsUnit ((2 : ZMod 3659) ^ 1829 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1829 : ZMod 3659)
      decide
    · change IsUnit ((2 : ZMod 3659) ^ 118 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3320 : ZMod 3659)
      decide
    · change IsUnit ((2 : ZMod 3659) ^ 62 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (446 : ZMod 3659)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3671 : Nat.Prime 3671 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3671 3670 1 13 [2, 5, 367]
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
    · change IsUnit ((13 : ZMod 3671) ^ 1835 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1835 : ZMod 3671)
      decide
    · change IsUnit ((13 : ZMod 3671) ^ 734 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3015 : ZMod 3671)
      decide
    · change IsUnit ((13 : ZMod 3671) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1851 : ZMod 3671)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3673 : Nat.Prime 3673 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3673 3672 1 5 [2, 2, 2, 3, 3, 3, 17]
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
    · change IsUnit ((5 : ZMod 3673) ^ 1836 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1836 : ZMod 3673)
      decide
    · change IsUnit ((5 : ZMod 3673) ^ 1836 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1836 : ZMod 3673)
      decide
    · change IsUnit ((5 : ZMod 3673) ^ 1836 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1836 : ZMod 3673)
      decide
    · change IsUnit ((5 : ZMod 3673) ^ 1224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2832 : ZMod 3673)
      decide
    · change IsUnit ((5 : ZMod 3673) ^ 1224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2832 : ZMod 3673)
      decide
    · change IsUnit ((5 : ZMod 3673) ^ 1224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2832 : ZMod 3673)
      decide
    · change IsUnit ((5 : ZMod 3673) ^ 216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2110 : ZMod 3673)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3677 : Nat.Prime 3677 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3677 3676 1 2 [2, 2, 919]
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
    · change IsUnit ((2 : ZMod 3677) ^ 1838 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1838 : ZMod 3677)
      decide
    · change IsUnit ((2 : ZMod 3677) ^ 1838 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1838 : ZMod 3677)
      decide
    · change IsUnit ((2 : ZMod 3677) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1716 : ZMod 3677)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3691 : Nat.Prime 3691 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3691 3690 1 2 [2, 3, 3, 5, 41]
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
    · change IsUnit ((2 : ZMod 3691) ^ 1845 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1845 : ZMod 3691)
      decide
    · change IsUnit ((2 : ZMod 3691) ^ 1230 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1388 : ZMod 3691)
      decide
    · change IsUnit ((2 : ZMod 3691) ^ 1230 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1388 : ZMod 3691)
      decide
    · change IsUnit ((2 : ZMod 3691) ^ 738 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1857 : ZMod 3691)
      decide
    · change IsUnit ((2 : ZMod 3691) ^ 90 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3027 : ZMod 3691)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3697 : Nat.Prime 3697 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3697 3696 1 5 [2, 2, 2, 2, 3, 7, 11]
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
    · change IsUnit ((5 : ZMod 3697) ^ 1848 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1848 : ZMod 3697)
      decide
    · change IsUnit ((5 : ZMod 3697) ^ 1848 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1848 : ZMod 3697)
      decide
    · change IsUnit ((5 : ZMod 3697) ^ 1848 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1848 : ZMod 3697)
      decide
    · change IsUnit ((5 : ZMod 3697) ^ 1848 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1848 : ZMod 3697)
      decide
    · change IsUnit ((5 : ZMod 3697) ^ 1232 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2291 : ZMod 3697)
      decide
    · change IsUnit ((5 : ZMod 3697) ^ 528 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2433 : ZMod 3697)
      decide
    · change IsUnit ((5 : ZMod 3697) ^ 336 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3232 : ZMod 3697)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3701 : Nat.Prime 3701 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3701 3700 1 2 [2, 2, 5, 5, 37]
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
    · change IsUnit ((2 : ZMod 3701) ^ 1850 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1850 : ZMod 3701)
      decide
    · change IsUnit ((2 : ZMod 3701) ^ 1850 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1850 : ZMod 3701)
      decide
    · change IsUnit ((2 : ZMod 3701) ^ 740 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (465 : ZMod 3701)
      decide
    · change IsUnit ((2 : ZMod 3701) ^ 740 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (465 : ZMod 3701)
      decide
    · change IsUnit ((2 : ZMod 3701) ^ 100 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2101 : ZMod 3701)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3709 : Nat.Prime 3709 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3709 3708 1 2 [2, 2, 3, 3, 103]
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
    · change IsUnit ((2 : ZMod 3709) ^ 1854 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1854 : ZMod 3709)
      decide
    · change IsUnit ((2 : ZMod 3709) ^ 1854 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1854 : ZMod 3709)
      decide
    · change IsUnit ((2 : ZMod 3709) ^ 1236 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2306 : ZMod 3709)
      decide
    · change IsUnit ((2 : ZMod 3709) ^ 1236 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2306 : ZMod 3709)
      decide
    · change IsUnit ((2 : ZMod 3709) ^ 36 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2326 : ZMod 3709)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3643) (q := 3659) (by exact lowPrime_3659) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3659) (q := 3671) (by exact lowPrime_3671) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3671) (q := 3673) (by exact lowPrime_3673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3673) (q := 3677) (by exact lowPrime_3677) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3677) (q := 3691) (by exact lowPrime_3691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3691) (q := 3697) (by exact lowPrime_3697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3697) (q := 3701) (by exact lowPrime_3701) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3701) (q := 3709) (by exact lowPrime_3709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part07_chain :
    DusartPrimeRowsChain 3643 3709 dusartPrimeRows_3275_3802_part07 := by
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
