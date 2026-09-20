import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 100 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_9631 : Nat.Prime 9631 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9631 9630 1 3 [2, 3, 3, 5, 107]
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
    · change IsUnit ((3 : ZMod 9631) ^ 4815 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4815 : ZMod 9631)
      decide
    · change IsUnit ((3 : ZMod 9631) ^ 3210 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (540 : ZMod 9631)
      decide
    · change IsUnit ((3 : ZMod 9631) ^ 3210 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (540 : ZMod 9631)
      decide
    · change IsUnit ((3 : ZMod 9631) ^ 1926 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7676 : ZMod 9631)
      decide
    · change IsUnit ((3 : ZMod 9631) ^ 90 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4692 : ZMod 9631)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9643 : Nat.Prime 9643 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9643 9642 1 2 [2, 3, 1607]
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
    · change IsUnit ((2 : ZMod 9643) ^ 4821 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4821 : ZMod 9643)
      decide
    · change IsUnit ((2 : ZMod 9643) ^ 3214 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4896 : ZMod 9643)
      decide
    · change IsUnit ((2 : ZMod 9643) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7194 : ZMod 9643)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9649 : Nat.Prime 9649 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9649 9648 1 7 [2, 2, 2, 2, 3, 3, 67]
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
    · change IsUnit ((7 : ZMod 9649) ^ 4824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4824 : ZMod 9649)
      decide
    · change IsUnit ((7 : ZMod 9649) ^ 4824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4824 : ZMod 9649)
      decide
    · change IsUnit ((7 : ZMod 9649) ^ 4824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4824 : ZMod 9649)
      decide
    · change IsUnit ((7 : ZMod 9649) ^ 4824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4824 : ZMod 9649)
      decide
    · change IsUnit ((7 : ZMod 9649) ^ 3216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1138 : ZMod 9649)
      decide
    · change IsUnit ((7 : ZMod 9649) ^ 3216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1138 : ZMod 9649)
      decide
    · change IsUnit ((7 : ZMod 9649) ^ 144 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5118 : ZMod 9649)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9661 : Nat.Prime 9661 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9661 9660 1 2 [2, 2, 3, 5, 7, 23]
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
    · change IsUnit ((2 : ZMod 9661) ^ 4830 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4830 : ZMod 9661)
      decide
    · change IsUnit ((2 : ZMod 9661) ^ 4830 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4830 : ZMod 9661)
      decide
    · change IsUnit ((2 : ZMod 9661) ^ 3220 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5889 : ZMod 9661)
      decide
    · change IsUnit ((2 : ZMod 9661) ^ 1932 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8128 : ZMod 9661)
      decide
    · change IsUnit ((2 : ZMod 9661) ^ 1380 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2986 : ZMod 9661)
      decide
    · change IsUnit ((2 : ZMod 9661) ^ 420 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1303 : ZMod 9661)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9677 : Nat.Prime 9677 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9677 9676 1 2 [2, 2, 41, 59]
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
    · change IsUnit ((2 : ZMod 9677) ^ 4838 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4838 : ZMod 9677)
      decide
    · change IsUnit ((2 : ZMod 9677) ^ 4838 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4838 : ZMod 9677)
      decide
    · change IsUnit ((2 : ZMod 9677) ^ 236 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1571 : ZMod 9677)
      decide
    · change IsUnit ((2 : ZMod 9677) ^ 164 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9626 : ZMod 9677)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9679 : Nat.Prime 9679 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9679 9678 1 3 [2, 3, 1613]
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
    · change IsUnit ((3 : ZMod 9679) ^ 4839 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4839 : ZMod 9679)
      decide
    · change IsUnit ((3 : ZMod 9679) ^ 3226 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5481 : ZMod 9679)
      decide
    · change IsUnit ((3 : ZMod 9679) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2566 : ZMod 9679)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9689 : Nat.Prime 9689 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9689 9688 1 3 [2, 2, 2, 7, 173]
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
    · change IsUnit ((3 : ZMod 9689) ^ 4844 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4844 : ZMod 9689)
      decide
    · change IsUnit ((3 : ZMod 9689) ^ 4844 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4844 : ZMod 9689)
      decide
    · change IsUnit ((3 : ZMod 9689) ^ 4844 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4844 : ZMod 9689)
      decide
    · change IsUnit ((3 : ZMod 9689) ^ 1384 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4638 : ZMod 9689)
      decide
    · change IsUnit ((3 : ZMod 9689) ^ 56 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5970 : ZMod 9689)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9697 : Nat.Prime 9697 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9697 9696 1 10 [2, 2, 2, 2, 2, 3, 101]
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
    · change IsUnit ((10 : ZMod 9697) ^ 4848 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4848 : ZMod 9697)
      decide
    · change IsUnit ((10 : ZMod 9697) ^ 4848 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4848 : ZMod 9697)
      decide
    · change IsUnit ((10 : ZMod 9697) ^ 4848 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4848 : ZMod 9697)
      decide
    · change IsUnit ((10 : ZMod 9697) ^ 4848 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4848 : ZMod 9697)
      decide
    · change IsUnit ((10 : ZMod 9697) ^ 4848 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4848 : ZMod 9697)
      decide
    · change IsUnit ((10 : ZMod 9697) ^ 3232 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7128 : ZMod 9697)
      decide
    · change IsUnit ((10 : ZMod 9697) ^ 96 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1400 : ZMod 9697)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9629) (q := 9631) (by exact lowPrime_9631) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9631) (q := 9643) (by exact lowPrime_9643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9643) (q := 9649) (by exact lowPrime_9649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9649) (q := 9661) (by exact lowPrime_9661) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9661) (q := 9677) (by exact lowPrime_9677) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9677) (q := 9679) (by exact lowPrime_9679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9679) (q := 9689) (by exact lowPrime_9689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9689) (q := 9697) (by exact lowPrime_9697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part04_chain :
    DusartPrimeRowsChain 9629 9697 dusartPrimeRows_9419_9900_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num
