import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 215 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22901 : Nat.Prime 22901 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22901 22900 1 2 [2, 2, 5, 5, 229]
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
    · apply IsUnit.of_mul_eq_one (11450 : ZMod 22901)
      decide
    · apply IsUnit.of_mul_eq_one (15056 : ZMod 22901)
      decide
    · apply IsUnit.of_mul_eq_one (15651 : ZMod 22901)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22907 : Nat.Prime 22907 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22907 22906 1 5 [2, 13, 881]
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
    · apply IsUnit.of_mul_eq_one (11453 : ZMod 22907)
      decide
    · apply IsUnit.of_mul_eq_one (19813 : ZMod 22907)
      decide
    · apply IsUnit.of_mul_eq_one (14995 : ZMod 22907)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22921 : Nat.Prime 22921 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22921 22920 1 7 [2, 2, 2, 3, 5, 191]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (11460 : ZMod 22921)
      decide
    · apply IsUnit.of_mul_eq_one (2817 : ZMod 22921)
      decide
    · apply IsUnit.of_mul_eq_one (350 : ZMod 22921)
      decide
    · apply IsUnit.of_mul_eq_one (12084 : ZMod 22921)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22937 : Nat.Prime 22937 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22937 22936 1 3 [2, 2, 2, 47, 61]
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
    · apply IsUnit.of_mul_eq_one (11468 : ZMod 22937)
      decide
    · apply IsUnit.of_mul_eq_one (20600 : ZMod 22937)
      decide
    · apply IsUnit.of_mul_eq_one (1295 : ZMod 22937)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22943 : Nat.Prime 22943 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22943 22942 1 5 [2, 11471]
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
    · apply IsUnit.of_mul_eq_one (11471 : ZMod 22943)
      decide
    · apply IsUnit.of_mul_eq_one (956 : ZMod 22943)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22961 : Nat.Prime 22961 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22961 22960 1 6 [2, 2, 2, 2, 5, 7, 41]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (11480 : ZMod 22961)
      decide
    · apply IsUnit.of_mul_eq_one (16506 : ZMod 22961)
      decide
    · apply IsUnit.of_mul_eq_one (11552 : ZMod 22961)
      decide
    · apply IsUnit.of_mul_eq_one (16694 : ZMod 22961)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22963 : Nat.Prime 22963 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22963 22962 1 3 [2, 3, 43, 89]
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
    · apply IsUnit.of_mul_eq_one (11481 : ZMod 22963)
      decide
    · apply IsUnit.of_mul_eq_one (20807 : ZMod 22963)
      decide
    · apply IsUnit.of_mul_eq_one (4131 : ZMod 22963)
      decide
    · apply IsUnit.of_mul_eq_one (5759 : ZMod 22963)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22973 : Nat.Prime 22973 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22973 22972 1 2 [2, 2, 5743]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (11486 : ZMod 22973)
      decide
    · apply IsUnit.of_mul_eq_one (19910 : ZMod 22973)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22877) (q := 22901) (by exact lowPrime_22901) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22901) (q := 22907) (by exact lowPrime_22907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22907) (q := 22921) (by exact lowPrime_22921) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22921) (q := 22937) (by exact lowPrime_22937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22937) (q := 22943) (by exact lowPrime_22943) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22943) (q := 22961) (by exact lowPrime_22961) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22961) (q := 22963) (by exact lowPrime_22963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22963) (q := 22973) (by exact lowPrime_22973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part12_chain :
    DusartPrimeRowsChain 22877 22972 dusartPrimeRows_22027_23158_part12 := by
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
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]
