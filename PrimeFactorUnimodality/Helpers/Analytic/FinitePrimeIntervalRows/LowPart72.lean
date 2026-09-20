import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 72 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_7817 : Nat.Prime 7817 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7817 7816 1 3 [2, 2, 2, 977]
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
    · change IsUnit ((3 : ZMod 7817) ^ 3908 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3908 : ZMod 7817)
      decide
    · change IsUnit ((3 : ZMod 7817) ^ 3908 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3908 : ZMod 7817)
      decide
    · change IsUnit ((3 : ZMod 7817) ^ 3908 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3908 : ZMod 7817)
      decide
    · change IsUnit ((3 : ZMod 7817) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (199 : ZMod 7817)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7823 : Nat.Prime 7823 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7823 7822 1 5 [2, 3911]
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
    · change IsUnit ((5 : ZMod 7823) ^ 3911 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3911 : ZMod 7823)
      decide
    · change IsUnit ((5 : ZMod 7823) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (326 : ZMod 7823)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7829 : Nat.Prime 7829 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7829 7828 1 2 [2, 2, 19, 103]
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
    · change IsUnit ((2 : ZMod 7829) ^ 3914 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3914 : ZMod 7829)
      decide
    · change IsUnit ((2 : ZMod 7829) ^ 3914 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3914 : ZMod 7829)
      decide
    · change IsUnit ((2 : ZMod 7829) ^ 412 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6811 : ZMod 7829)
      decide
    · change IsUnit ((2 : ZMod 7829) ^ 76 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2733 : ZMod 7829)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7841 : Nat.Prime 7841 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7841 7840 1 12 [2, 2, 2, 2, 2, 5, 7, 7]
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
    · change IsUnit ((12 : ZMod 7841) ^ 3920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3920 : ZMod 7841)
      decide
    · change IsUnit ((12 : ZMod 7841) ^ 3920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3920 : ZMod 7841)
      decide
    · change IsUnit ((12 : ZMod 7841) ^ 3920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3920 : ZMod 7841)
      decide
    · change IsUnit ((12 : ZMod 7841) ^ 3920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3920 : ZMod 7841)
      decide
    · change IsUnit ((12 : ZMod 7841) ^ 3920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3920 : ZMod 7841)
      decide
    · change IsUnit ((12 : ZMod 7841) ^ 1568 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1195 : ZMod 7841)
      decide
    · change IsUnit ((12 : ZMod 7841) ^ 1120 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2473 : ZMod 7841)
      decide
    · change IsUnit ((12 : ZMod 7841) ^ 1120 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2473 : ZMod 7841)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7853 : Nat.Prime 7853 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7853 7852 1 2 [2, 2, 13, 151]
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
    · change IsUnit ((2 : ZMod 7853) ^ 3926 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3926 : ZMod 7853)
      decide
    · change IsUnit ((2 : ZMod 7853) ^ 3926 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3926 : ZMod 7853)
      decide
    · change IsUnit ((2 : ZMod 7853) ^ 604 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5013 : ZMod 7853)
      decide
    · change IsUnit ((2 : ZMod 7853) ^ 52 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5732 : ZMod 7853)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7867 : Nat.Prime 7867 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7867 7866 1 3 [2, 3, 3, 19, 23]
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
    · change IsUnit ((3 : ZMod 7867) ^ 3933 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3933 : ZMod 7867)
      decide
    · change IsUnit ((3 : ZMod 7867) ^ 2622 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7378 : ZMod 7867)
      decide
    · change IsUnit ((3 : ZMod 7867) ^ 2622 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7378 : ZMod 7867)
      decide
    · change IsUnit ((3 : ZMod 7867) ^ 414 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6739 : ZMod 7867)
      decide
    · change IsUnit ((3 : ZMod 7867) ^ 342 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5227 : ZMod 7867)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7873 : Nat.Prime 7873 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7873 7872 1 5 [2, 2, 2, 2, 2, 2, 3, 41]
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
    · change IsUnit ((5 : ZMod 7873) ^ 3936 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3936 : ZMod 7873)
      decide
    · change IsUnit ((5 : ZMod 7873) ^ 3936 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3936 : ZMod 7873)
      decide
    · change IsUnit ((5 : ZMod 7873) ^ 3936 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3936 : ZMod 7873)
      decide
    · change IsUnit ((5 : ZMod 7873) ^ 3936 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3936 : ZMod 7873)
      decide
    · change IsUnit ((5 : ZMod 7873) ^ 3936 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3936 : ZMod 7873)
      decide
    · change IsUnit ((5 : ZMod 7873) ^ 3936 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3936 : ZMod 7873)
      decide
    · change IsUnit ((5 : ZMod 7873) ^ 2624 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5713 : ZMod 7873)
      decide
    · change IsUnit ((5 : ZMod 7873) ^ 192 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4507 : ZMod 7873)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7877 : Nat.Prime 7877 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7877 7876 1 2 [2, 2, 11, 179]
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
    · change IsUnit ((2 : ZMod 7877) ^ 3938 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3938 : ZMod 7877)
      decide
    · change IsUnit ((2 : ZMod 7877) ^ 3938 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3938 : ZMod 7877)
      decide
    · change IsUnit ((2 : ZMod 7877) ^ 716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4769 : ZMod 7877)
      decide
    · change IsUnit ((2 : ZMod 7877) ^ 44 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5211 : ZMod 7877)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7793) (q := 7817) (by exact lowPrime_7817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7817) (q := 7823) (by exact lowPrime_7823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7823) (q := 7829) (by exact lowPrime_7829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7829) (q := 7841) (by exact lowPrime_7841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7841) (q := 7853) (by exact lowPrime_7853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7853) (q := 7867) (by exact lowPrime_7867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7867) (q := 7873) (by exact lowPrime_7873) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7873) (q := 7877) (by exact lowPrime_7877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part02_chain :
    DusartPrimeRowsChain 7793 7877 dusartPrimeRows_7717_8110_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num
