import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 156 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13693 : Nat.Prime 13693 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13693 13692 1 6 [2, 2, 3, 7, 163]
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
    · apply IsUnit.of_mul_eq_one (6846 : ZMod 13693)
      decide
    · apply IsUnit.of_mul_eq_one (3561 : ZMod 13693)
      decide
    · apply IsUnit.of_mul_eq_one (12349 : ZMod 13693)
      decide
    · apply IsUnit.of_mul_eq_one (5523 : ZMod 13693)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13697 : Nat.Prime 13697 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13697 13696 1 3 [2, 2, 2, 2, 2, 2, 2, 107]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6848 : ZMod 13697)
      decide
    · apply IsUnit.of_mul_eq_one (1923 : ZMod 13697)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13709 : Nat.Prime 13709 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13709 13708 1 2 [2, 2, 23, 149]
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
    · apply IsUnit.of_mul_eq_one (6854 : ZMod 13709)
      decide
    · apply IsUnit.of_mul_eq_one (11514 : ZMod 13709)
      decide
    · apply IsUnit.of_mul_eq_one (9931 : ZMod 13709)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13711 : Nat.Prime 13711 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13711 13710 1 6 [2, 3, 5, 457]
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
    · apply IsUnit.of_mul_eq_one (6855 : ZMod 13711)
      decide
    · apply IsUnit.of_mul_eq_one (1049 : ZMod 13711)
      decide
    · apply IsUnit.of_mul_eq_one (2811 : ZMod 13711)
      decide
    · apply IsUnit.of_mul_eq_one (597 : ZMod 13711)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13721 : Nat.Prime 13721 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13721 13720 1 3 [2, 2, 2, 5, 7, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (6860 : ZMod 13721)
      decide
    · apply IsUnit.of_mul_eq_one (10624 : ZMod 13721)
      decide
    · apply IsUnit.of_mul_eq_one (5353 : ZMod 13721)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13723 : Nat.Prime 13723 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13723 13722 1 2 [2, 3, 2287]
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
    · apply IsUnit.of_mul_eq_one (6861 : ZMod 13723)
      decide
    · apply IsUnit.of_mul_eq_one (3857 : ZMod 13723)
      decide
    · apply IsUnit.of_mul_eq_one (5010 : ZMod 13723)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13729 : Nat.Prime 13729 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13729 13728 1 23 [2, 2, 2, 2, 2, 3, 11, 13]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6864 : ZMod 13729)
      decide
    · apply IsUnit.of_mul_eq_one (2236 : ZMod 13729)
      decide
    · apply IsUnit.of_mul_eq_one (12927 : ZMod 13729)
      decide
    · apply IsUnit.of_mul_eq_one (294 : ZMod 13729)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13751 : Nat.Prime 13751 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13751 13750 1 11 [2, 5, 5, 5, 5, 11]
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
    · apply IsUnit.of_mul_eq_one (6875 : ZMod 13751)
      decide
    · apply IsUnit.of_mul_eq_one (1728 : ZMod 13751)
      decide
    · apply IsUnit.of_mul_eq_one (5381 : ZMod 13751)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13691) (q := 13693) (by exact lowPrime_13693) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13693) (q := 13697) (by exact lowPrime_13697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13697) (q := 13709) (by exact lowPrime_13709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13709) (q := 13711) (by exact lowPrime_13711) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13711) (q := 13721) (by exact lowPrime_13721) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13721) (q := 13723) (by exact lowPrime_13723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13723) (q := 13729) (by exact lowPrime_13729) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13729) (q := 13751) (by exact lowPrime_13751) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part05_chain :
    DusartPrimeRowsChain 13691 13750 dusartPrimeRows_13367_14050_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]
