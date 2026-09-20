import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 114 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_10657 : Nat.Prime 10657 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10657 10656 1 7 [2, 2, 2, 2, 2, 3, 3, 37]
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
    · change IsUnit ((7 : ZMod 10657) ^ 5328 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5328 : ZMod 10657)
      decide
    · change IsUnit ((7 : ZMod 10657) ^ 5328 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5328 : ZMod 10657)
      decide
    · change IsUnit ((7 : ZMod 10657) ^ 5328 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5328 : ZMod 10657)
      decide
    · change IsUnit ((7 : ZMod 10657) ^ 5328 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5328 : ZMod 10657)
      decide
    · change IsUnit ((7 : ZMod 10657) ^ 5328 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5328 : ZMod 10657)
      decide
    · change IsUnit ((7 : ZMod 10657) ^ 3552 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8432 : ZMod 10657)
      decide
    · change IsUnit ((7 : ZMod 10657) ^ 3552 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8432 : ZMod 10657)
      decide
    · change IsUnit ((7 : ZMod 10657) ^ 288 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3738 : ZMod 10657)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10663 : Nat.Prime 10663 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10663 10662 1 3 [2, 3, 1777]
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
    · change IsUnit ((3 : ZMod 10663) ^ 5331 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5331 : ZMod 10663)
      decide
    · change IsUnit ((3 : ZMod 10663) ^ 3554 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7377 : ZMod 10663)
      decide
    · change IsUnit ((3 : ZMod 10663) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (249 : ZMod 10663)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10667 : Nat.Prime 10667 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10667 10666 1 2 [2, 5333]
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
    · change IsUnit ((2 : ZMod 10667) ^ 5333 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5333 : ZMod 10667)
      decide
    · change IsUnit ((2 : ZMod 10667) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3556 : ZMod 10667)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10687 : Nat.Prime 10687 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10687 10686 1 5 [2, 3, 13, 137]
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
    · change IsUnit ((5 : ZMod 10687) ^ 5343 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5343 : ZMod 10687)
      decide
    · change IsUnit ((5 : ZMod 10687) ^ 3562 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8342 : ZMod 10687)
      decide
    · change IsUnit ((5 : ZMod 10687) ^ 822 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6726 : ZMod 10687)
      decide
    · change IsUnit ((5 : ZMod 10687) ^ 78 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5794 : ZMod 10687)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10691 : Nat.Prime 10691 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10691 10690 1 2 [2, 5, 1069]
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
    · change IsUnit ((2 : ZMod 10691) ^ 5345 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5345 : ZMod 10691)
      decide
    · change IsUnit ((2 : ZMod 10691) ^ 2138 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5213 : ZMod 10691)
      decide
    · change IsUnit ((2 : ZMod 10691) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6563 : ZMod 10691)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10709 : Nat.Prime 10709 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10709 10708 1 2 [2, 2, 2677]
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
    · change IsUnit ((2 : ZMod 10709) ^ 5354 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5354 : ZMod 10709)
      decide
    · change IsUnit ((2 : ZMod 10709) ^ 5354 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5354 : ZMod 10709)
      decide
    · change IsUnit ((2 : ZMod 10709) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (714 : ZMod 10709)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10711 : Nat.Prime 10711 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10711 10710 1 3 [2, 3, 3, 5, 7, 17]
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
    · change IsUnit ((3 : ZMod 10711) ^ 5355 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5355 : ZMod 10711)
      decide
    · change IsUnit ((3 : ZMod 10711) ^ 3570 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5640 : ZMod 10711)
      decide
    · change IsUnit ((3 : ZMod 10711) ^ 3570 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5640 : ZMod 10711)
      decide
    · change IsUnit ((3 : ZMod 10711) ^ 2142 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10234 : ZMod 10711)
      decide
    · change IsUnit ((3 : ZMod 10711) ^ 1530 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8233 : ZMod 10711)
      decide
    · change IsUnit ((3 : ZMod 10711) ^ 630 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2620 : ZMod 10711)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10723 : Nat.Prime 10723 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10723 10722 1 2 [2, 3, 1787]
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
    · change IsUnit ((2 : ZMod 10723) ^ 5361 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5361 : ZMod 10723)
      decide
    · change IsUnit ((2 : ZMod 10723) ^ 3574 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10304 : ZMod 10723)
      decide
    · change IsUnit ((2 : ZMod 10723) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4936 : ZMod 10723)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10651) (q := 10657) (by exact lowPrime_10657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10657) (q := 10663) (by exact lowPrime_10663) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10663) (q := 10667) (by exact lowPrime_10667) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10667) (q := 10687) (by exact lowPrime_10687) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10687) (q := 10691) (by exact lowPrime_10691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10691) (q := 10709) (by exact lowPrime_10709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10709) (q := 10711) (by exact lowPrime_10711) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10711) (q := 10723) (by exact lowPrime_10723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part04_chain :
    DusartPrimeRowsChain 10651 10723 dusartPrimeRows_10427_10938_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10938]
              · norm_num [dusartPrimeRow_of_explicit_10938]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10938]
                · norm_num [dusartPrimeRow_of_explicit_10938]
                · apply DusartPrimeRowsChain.empty
                  norm_num
