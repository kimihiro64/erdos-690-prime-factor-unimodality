import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 266 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18539 : Nat.Prime 18539 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18539 18538 1 6 [2, 13, 23, 31]
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
    · apply IsUnit.of_mul_eq_one (9269 : ZMod 18539)
      decide
    · apply IsUnit.of_mul_eq_one (923 : ZMod 18539)
      decide
    · apply IsUnit.of_mul_eq_one (8637 : ZMod 18539)
      decide
    · apply IsUnit.of_mul_eq_one (8127 : ZMod 18539)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18541 : Nat.Prime 18541 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18541 18540 1 6 [2, 2, 3, 3, 5, 103]
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
    · apply IsUnit.of_mul_eq_one (9270 : ZMod 18541)
      decide
    · apply IsUnit.of_mul_eq_one (7091 : ZMod 18541)
      decide
    · apply IsUnit.of_mul_eq_one (6191 : ZMod 18541)
      decide
    · apply IsUnit.of_mul_eq_one (13871 : ZMod 18541)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18553 : Nat.Prime 18553 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18553 18552 1 5 [2, 2, 2, 3, 773]
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
    · apply IsUnit.of_mul_eq_one (9276 : ZMod 18553)
      decide
    · apply IsUnit.of_mul_eq_one (9805 : ZMod 18553)
      decide
    · apply IsUnit.of_mul_eq_one (1722 : ZMod 18553)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18583 : Nat.Prime 18583 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18583 18582 1 3 [2, 3, 19, 163]
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
    · apply IsUnit.of_mul_eq_one (9291 : ZMod 18583)
      decide
    · apply IsUnit.of_mul_eq_one (8204 : ZMod 18583)
      decide
    · apply IsUnit.of_mul_eq_one (15045 : ZMod 18583)
      decide
    · apply IsUnit.of_mul_eq_one (14429 : ZMod 18583)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18587 : Nat.Prime 18587 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18587 18586 1 2 [2, 9293]
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
    · apply IsUnit.of_mul_eq_one (9293 : ZMod 18587)
      decide
    · apply IsUnit.of_mul_eq_one (6196 : ZMod 18587)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18593 : Nat.Prime 18593 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18593 18592 1 3 [2, 2, 2, 2, 2, 7, 83]
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
    · apply IsUnit.of_mul_eq_one (9296 : ZMod 18593)
      decide
    · apply IsUnit.of_mul_eq_one (10267 : ZMod 18593)
      decide
    · apply IsUnit.of_mul_eq_one (2167 : ZMod 18593)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18617 : Nat.Prime 18617 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18617 18616 1 3 [2, 2, 2, 13, 179]
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
    · apply IsUnit.of_mul_eq_one (9308 : ZMod 18617)
      decide
    · apply IsUnit.of_mul_eq_one (13446 : ZMod 18617)
      decide
    · apply IsUnit.of_mul_eq_one (2884 : ZMod 18617)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18637 : Nat.Prime 18637 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18637 18636 1 2 [2, 2, 3, 1553]
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
    · apply IsUnit.of_mul_eq_one (9318 : ZMod 18637)
      decide
    · apply IsUnit.of_mul_eq_one (12886 : ZMod 18637)
      decide
    · apply IsUnit.of_mul_eq_one (15301 : ZMod 18637)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18523) (q := 18539) (by exact lowPrime_18539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18539) (q := 18541) (by exact lowPrime_18541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18541) (q := 18553) (by exact lowPrime_18553) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18553) (q := 18583) (by exact lowPrime_18583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18583) (q := 18587) (by exact lowPrime_18587) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18587) (q := 18593) (by exact lowPrime_18593) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18593) (q := 18617) (by exact lowPrime_18617) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18617) (q := 18637) (by exact lowPrime_18637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part08_chain :
    DusartPrimeRowsChain 18523 18636 dusartPrimeRows_18041_18958_part08 := by
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
