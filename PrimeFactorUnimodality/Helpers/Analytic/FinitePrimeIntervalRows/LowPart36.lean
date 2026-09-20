import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 36 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5503 : Nat.Prime 5503 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5503 5502 1 3 [2, 3, 7, 131]
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
    · apply IsUnit.of_mul_eq_one (2751 : ZMod 5503)
      decide
    · apply IsUnit.of_mul_eq_one (3978 : ZMod 5503)
      decide
    · apply IsUnit.of_mul_eq_one (4163 : ZMod 5503)
      decide
    · apply IsUnit.of_mul_eq_one (2529 : ZMod 5503)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5507 : Nat.Prime 5507 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5507 5506 1 2 [2, 2753]
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
    · apply IsUnit.of_mul_eq_one (2753 : ZMod 5507)
      decide
    · apply IsUnit.of_mul_eq_one (1836 : ZMod 5507)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5519 : Nat.Prime 5519 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5519 5518 1 13 [2, 31, 89]
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
    · apply IsUnit.of_mul_eq_one (2759 : ZMod 5519)
      decide
    · apply IsUnit.of_mul_eq_one (2745 : ZMod 5519)
      decide
    · apply IsUnit.of_mul_eq_one (943 : ZMod 5519)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5521 : Nat.Prime 5521 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5521 5520 1 11 [2, 2, 2, 2, 3, 5, 23]
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
    · apply IsUnit.of_mul_eq_one (2760 : ZMod 5521)
      decide
    · apply IsUnit.of_mul_eq_one (113 : ZMod 5521)
      decide
    · apply IsUnit.of_mul_eq_one (571 : ZMod 5521)
      decide
    · apply IsUnit.of_mul_eq_one (2270 : ZMod 5521)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5527 : Nat.Prime 5527 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5527 5526 1 5 [2, 3, 3, 307]
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
    · apply IsUnit.of_mul_eq_one (2763 : ZMod 5527)
      decide
    · apply IsUnit.of_mul_eq_one (3392 : ZMod 5527)
      decide
    · apply IsUnit.of_mul_eq_one (4760 : ZMod 5527)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5531 : Nat.Prime 5531 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5531 5530 1 10 [2, 5, 7, 79]
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
    · apply IsUnit.of_mul_eq_one (2765 : ZMod 5531)
      decide
    · apply IsUnit.of_mul_eq_one (2080 : ZMod 5531)
      decide
    · apply IsUnit.of_mul_eq_one (2446 : ZMod 5531)
      decide
    · apply IsUnit.of_mul_eq_one (733 : ZMod 5531)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5557 : Nat.Prime 5557 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5557 5556 1 2 [2, 2, 3, 463]
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
    · apply IsUnit.of_mul_eq_one (2778 : ZMod 5557)
      decide
    · apply IsUnit.of_mul_eq_one (3095 : ZMod 5557)
      decide
    · apply IsUnit.of_mul_eq_one (3972 : ZMod 5557)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5563 : Nat.Prime 5563 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5563 5562 1 2 [2, 3, 3, 3, 103]
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
    · apply IsUnit.of_mul_eq_one (2781 : ZMod 5563)
      decide
    · apply IsUnit.of_mul_eq_one (3471 : ZMod 5563)
      decide
    · apply IsUnit.of_mul_eq_one (5473 : ZMod 5563)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5501) (q := 5503) (by exact lowPrime_5503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5503) (q := 5507) (by exact lowPrime_5507) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5507) (q := 5519) (by exact lowPrime_5519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5519) (q := 5521) (by exact lowPrime_5521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5521) (q := 5527) (by exact lowPrime_5527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5527) (q := 5531) (by exact lowPrime_5531) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5531) (q := 5557) (by exact lowPrime_5557) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5557) (q := 5563) (by exact lowPrime_5563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part02_chain :
    DusartPrimeRowsChain 5501 5562 dusartPrimeRows_5437_5710_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5710]
      · norm_num [dusartPrimeRow_of_explicit_5710]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5710]
        · norm_num [dusartPrimeRow_of_explicit_5710]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5710]
          · norm_num [dusartPrimeRow_of_explicit_5710]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5710]
            · norm_num [dusartPrimeRow_of_explicit_5710]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5710]
              · norm_num [dusartPrimeRow_of_explicit_5710]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5710]
                · norm_num [dusartPrimeRow_of_explicit_5710]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5710, dusartPrimeRow_of_explicit_right]
