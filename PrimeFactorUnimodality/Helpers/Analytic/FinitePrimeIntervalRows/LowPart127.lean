import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 127 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11617 : Nat.Prime 11617 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11617 11616 1 10 [2, 2, 2, 2, 2, 3, 11, 11]
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
    · apply IsUnit.of_mul_eq_one (5808 : ZMod 11617)
      decide
    · apply IsUnit.of_mul_eq_one (864 : ZMod 11617)
      decide
    · apply IsUnit.of_mul_eq_one (844 : ZMod 11617)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11621 : Nat.Prime 11621 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11621 11620 1 2 [2, 2, 5, 7, 83]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5810 : ZMod 11621)
      decide
    · apply IsUnit.of_mul_eq_one (10691 : ZMod 11621)
      decide
    · apply IsUnit.of_mul_eq_one (8718 : ZMod 11621)
      decide
    · apply IsUnit.of_mul_eq_one (4674 : ZMod 11621)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11633 : Nat.Prime 11633 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11633 11632 1 3 [2, 2, 2, 2, 727]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (5816 : ZMod 11633)
      decide
    · apply IsUnit.of_mul_eq_one (5396 : ZMod 11633)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11657 : Nat.Prime 11657 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11657 11656 1 3 [2, 2, 2, 31, 47]
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
    · apply IsUnit.of_mul_eq_one (5828 : ZMod 11657)
      decide
    · apply IsUnit.of_mul_eq_one (10317 : ZMod 11657)
      decide
    · apply IsUnit.of_mul_eq_one (581 : ZMod 11657)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11677 : Nat.Prime 11677 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11677 11676 1 2 [2, 2, 3, 7, 139]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5838 : ZMod 11677)
      decide
    · apply IsUnit.of_mul_eq_one (719 : ZMod 11677)
      decide
    · apply IsUnit.of_mul_eq_one (1374 : ZMod 11677)
      decide
    · apply IsUnit.of_mul_eq_one (2345 : ZMod 11677)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11681 : Nat.Prime 11681 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11681 11680 1 3 [2, 2, 2, 2, 2, 5, 73]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5840 : ZMod 11681)
      decide
    · apply IsUnit.of_mul_eq_one (964 : ZMod 11681)
      decide
    · apply IsUnit.of_mul_eq_one (2303 : ZMod 11681)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11689 : Nat.Prime 11689 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11689 11688 1 7 [2, 2, 2, 3, 487]
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
    · apply IsUnit.of_mul_eq_one (5844 : ZMod 11689)
      decide
    · apply IsUnit.of_mul_eq_one (633 : ZMod 11689)
      decide
    · apply IsUnit.of_mul_eq_one (4027 : ZMod 11689)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11699 : Nat.Prime 11699 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11699 11698 1 2 [2, 5849]
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
    · apply IsUnit.of_mul_eq_one (5849 : ZMod 11699)
      decide
    · apply IsUnit.of_mul_eq_one (3900 : ZMod 11699)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11597) (q := 11617) (by exact lowPrime_11617) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11617) (q := 11621) (by exact lowPrime_11621) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11621) (q := 11633) (by exact lowPrime_11633) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11633) (q := 11657) (by exact lowPrime_11657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11657) (q := 11677) (by exact lowPrime_11677) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11677) (q := 11681) (by exact lowPrime_11681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11681) (q := 11689) (by exact lowPrime_11689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11689) (q := 11699) (by exact lowPrime_11699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part02_chain :
    DusartPrimeRowsChain 11597 11698 dusartPrimeRows_11503_12096_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12088, dusartPrimeRow_of_explicit_right]
