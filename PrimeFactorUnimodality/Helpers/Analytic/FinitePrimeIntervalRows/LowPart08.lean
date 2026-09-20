import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 08 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3719 : Nat.Prime 3719 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3719 3718 1 7 [2, 11, 13, 13]
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
    · apply IsUnit.of_mul_eq_one (1859 : ZMod 3719)
      decide
    · apply IsUnit.of_mul_eq_one (2161 : ZMod 3719)
      decide
    · apply IsUnit.of_mul_eq_one (2836 : ZMod 3719)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3727 : Nat.Prime 3727 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3727 3726 1 3 [2, 3, 3, 3, 3, 23]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (1863 : ZMod 3727)
      decide
    · apply IsUnit.of_mul_eq_one (1638 : ZMod 3727)
      decide
    · apply IsUnit.of_mul_eq_one (3421 : ZMod 3727)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3733 : Nat.Prime 3733 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3733 3732 1 2 [2, 2, 3, 311]
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
    · apply IsUnit.of_mul_eq_one (1866 : ZMod 3733)
      decide
    · apply IsUnit.of_mul_eq_one (2172 : ZMod 3733)
      decide
    · apply IsUnit.of_mul_eq_one (1949 : ZMod 3733)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3739 : Nat.Prime 3739 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3739 3738 1 7 [2, 3, 7, 89]
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
    · apply IsUnit.of_mul_eq_one (1869 : ZMod 3739)
      decide
    · apply IsUnit.of_mul_eq_one (231 : ZMod 3739)
      decide
    · apply IsUnit.of_mul_eq_one (2631 : ZMod 3739)
      decide
    · apply IsUnit.of_mul_eq_one (1859 : ZMod 3739)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3761 : Nat.Prime 3761 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3761 3760 1 3 [2, 2, 2, 2, 5, 47]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (1880 : ZMod 3761)
      decide
    · apply IsUnit.of_mul_eq_one (1947 : ZMod 3761)
      decide
    · apply IsUnit.of_mul_eq_one (1463 : ZMod 3761)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3767 : Nat.Prime 3767 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3767 3766 1 5 [2, 7, 269]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (1883 : ZMod 3767)
      decide
    · apply IsUnit.of_mul_eq_one (1788 : ZMod 3767)
      decide
    · apply IsUnit.of_mul_eq_one (2468 : ZMod 3767)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3769 : Nat.Prime 3769 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3769 3768 1 7 [2, 2, 2, 3, 157]
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
    · apply IsUnit.of_mul_eq_one (1884 : ZMod 3769)
      decide
    · apply IsUnit.of_mul_eq_one (154 : ZMod 3769)
      decide
    · apply IsUnit.of_mul_eq_one (3425 : ZMod 3769)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3779 : Nat.Prime 3779 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3779 3778 1 2 [2, 1889]
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
    · apply IsUnit.of_mul_eq_one (1889 : ZMod 3779)
      decide
    · apply IsUnit.of_mul_eq_one (1260 : ZMod 3779)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3709) (q := 3719) (by exact lowPrime_3719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3719) (q := 3727) (by exact lowPrime_3727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3727) (q := 3733) (by exact lowPrime_3733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3733) (q := 3739) (by exact lowPrime_3739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3739) (q := 3761) (by exact lowPrime_3761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3761) (q := 3767) (by exact lowPrime_3767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3767) (q := 3769) (by exact lowPrime_3769) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3769) (q := 3779) (by exact lowPrime_3779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part08_chain :
    DusartPrimeRowsChain 3709 3778 dusartPrimeRows_3275_3802_part08 := by
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
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]
