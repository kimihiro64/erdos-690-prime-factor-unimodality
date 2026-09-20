import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 248 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19157 : Nat.Prime 19157 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19157 19156 1 2 [2, 2, 4789]
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
    · apply IsUnit.of_mul_eq_one (9578 : ZMod 19157)
      decide
    · apply IsUnit.of_mul_eq_one (8940 : ZMod 19157)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19163 : Nat.Prime 19163 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19163 19162 1 2 [2, 11, 13, 67]
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
    · apply IsUnit.of_mul_eq_one (9581 : ZMod 19163)
      decide
    · apply IsUnit.of_mul_eq_one (7900 : ZMod 19163)
      decide
    · apply IsUnit.of_mul_eq_one (18356 : ZMod 19163)
      decide
    · apply IsUnit.of_mul_eq_one (16250 : ZMod 19163)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19181 : Nat.Prime 19181 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19181 19180 1 2 [2, 2, 5, 7, 137]
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
    · apply IsUnit.of_mul_eq_one (9590 : ZMod 19181)
      decide
    · apply IsUnit.of_mul_eq_one (7499 : ZMod 19181)
      decide
    · apply IsUnit.of_mul_eq_one (5024 : ZMod 19181)
      decide
    · apply IsUnit.of_mul_eq_one (1837 : ZMod 19181)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19183 : Nat.Prime 19183 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19183 19182 1 3 [2, 3, 23, 139]
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
    · apply IsUnit.of_mul_eq_one (9591 : ZMod 19183)
      decide
    · apply IsUnit.of_mul_eq_one (12742 : ZMod 19183)
      decide
    · apply IsUnit.of_mul_eq_one (12216 : ZMod 19183)
      decide
    · apply IsUnit.of_mul_eq_one (7845 : ZMod 19183)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19207 : Nat.Prime 19207 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19207 19206 1 5 [2, 3, 3, 11, 97]
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
    · apply IsUnit.of_mul_eq_one (9603 : ZMod 19207)
      decide
    · apply IsUnit.of_mul_eq_one (15276 : ZMod 19207)
      decide
    · apply IsUnit.of_mul_eq_one (10698 : ZMod 19207)
      decide
    · apply IsUnit.of_mul_eq_one (13005 : ZMod 19207)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19211 : Nat.Prime 19211 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19211 19210 1 6 [2, 5, 17, 113]
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
    · apply IsUnit.of_mul_eq_one (9605 : ZMod 19211)
      decide
    · apply IsUnit.of_mul_eq_one (11344 : ZMod 19211)
      decide
    · apply IsUnit.of_mul_eq_one (7973 : ZMod 19211)
      decide
    · apply IsUnit.of_mul_eq_one (14290 : ZMod 19211)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19213 : Nat.Prime 19213 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19213 19212 1 5 [2, 2, 3, 1601]
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
    · apply IsUnit.of_mul_eq_one (9606 : ZMod 19213)
      decide
    · apply IsUnit.of_mul_eq_one (3407 : ZMod 19213)
      decide
    · apply IsUnit.of_mul_eq_one (14433 : ZMod 19213)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19219 : Nat.Prime 19219 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19219 19218 1 2 [2, 3, 3203]
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
    · apply IsUnit.of_mul_eq_one (9609 : ZMod 19219)
      decide
    · apply IsUnit.of_mul_eq_one (10060 : ZMod 19219)
      decide
    · apply IsUnit.of_mul_eq_one (14338 : ZMod 19219)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19141) (q := 19157) (by exact lowPrime_19157) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19157) (q := 19163) (by exact lowPrime_19163) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19163) (q := 19181) (by exact lowPrime_19181) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19181) (q := 19183) (by exact lowPrime_19183) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19183) (q := 19207) (by exact lowPrime_19207) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19207) (q := 19211) (by exact lowPrime_19211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19211) (q := 19213) (by exact lowPrime_19213) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19213) (q := 19219) (by exact lowPrime_19219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part03_chain :
    DusartPrimeRowsChain 19141 19218 dusartPrimeRows_18959_19936_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]
