import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 268 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18743 : Nat.Prime 18743 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18743 18742 1 5 [2, 9371]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (9371 : ZMod 18743)
      decide
    · apply IsUnit.of_mul_eq_one (781 : ZMod 18743)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18749 : Nat.Prime 18749 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18749 18748 1 2 [2, 2, 43, 109]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (9374 : ZMod 18749)
      decide
    · apply IsUnit.of_mul_eq_one (3262 : ZMod 18749)
      decide
    · apply IsUnit.of_mul_eq_one (12720 : ZMod 18749)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18757 : Nat.Prime 18757 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18757 18756 1 2 [2, 2, 3, 3, 521]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (9378 : ZMod 18757)
      decide
    · apply IsUnit.of_mul_eq_one (7613 : ZMod 18757)
      decide
    · apply IsUnit.of_mul_eq_one (1858 : ZMod 18757)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18773 : Nat.Prime 18773 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18773 18772 1 2 [2, 2, 13, 19, 19]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (9386 : ZMod 18773)
      decide
    · apply IsUnit.of_mul_eq_one (8038 : ZMod 18773)
      decide
    · apply IsUnit.of_mul_eq_one (9050 : ZMod 18773)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18787 : Nat.Prime 18787 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18787 18786 1 2 [2, 3, 31, 101]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (9393 : ZMod 18787)
      decide
    · apply IsUnit.of_mul_eq_one (3527 : ZMod 18787)
      decide
    · apply IsUnit.of_mul_eq_one (9175 : ZMod 18787)
      decide
    · apply IsUnit.of_mul_eq_one (18714 : ZMod 18787)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18793 : Nat.Prime 18793 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18793 18792 1 5 [2, 2, 2, 3, 3, 3, 3, 29]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (9396 : ZMod 18793)
      decide
    · apply IsUnit.of_mul_eq_one (11810 : ZMod 18793)
      decide
    · apply IsUnit.of_mul_eq_one (4890 : ZMod 18793)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18797 : Nat.Prime 18797 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18797 18796 1 3 [2, 2, 37, 127]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (9398 : ZMod 18797)
      decide
    · apply IsUnit.of_mul_eq_one (17289 : ZMod 18797)
      decide
    · apply IsUnit.of_mul_eq_one (17111 : ZMod 18797)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18803 : Nat.Prime 18803 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18803 18802 1 5 [2, 7, 17, 79]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (9401 : ZMod 18803)
      decide
    · apply IsUnit.of_mul_eq_one (13310 : ZMod 18803)
      decide
    · apply IsUnit.of_mul_eq_one (12984 : ZMod 18803)
      decide
    · apply IsUnit.of_mul_eq_one (12069 : ZMod 18803)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18731) (q := 18743) (by exact lowPrime_18743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18743) (q := 18749) (by exact lowPrime_18749) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18749) (q := 18757) (by exact lowPrime_18757) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18757) (q := 18773) (by exact lowPrime_18773) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18773) (q := 18787) (by exact lowPrime_18787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18787) (q := 18793) (by exact lowPrime_18793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18793) (q := 18797) (by exact lowPrime_18797) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18797) (q := 18803) (by exact lowPrime_18803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part10_chain :
    DusartPrimeRowsChain 18731 18802 dusartPrimeRows_18041_18958_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]
