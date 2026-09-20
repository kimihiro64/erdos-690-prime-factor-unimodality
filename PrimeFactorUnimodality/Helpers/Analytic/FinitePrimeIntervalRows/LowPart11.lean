import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 11 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11519 : Nat.Prime 11519 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11519 11518 1 7 [2, 13, 443]
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
    · apply IsUnit.of_mul_eq_one (5759 : ZMod 11519)
      decide
    · apply IsUnit.of_mul_eq_one (258 : ZMod 11519)
      decide
    · apply IsUnit.of_mul_eq_one (3125 : ZMod 11519)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11527 : Nat.Prime 11527 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11527 11526 1 5 [2, 3, 17, 113]
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
    · apply IsUnit.of_mul_eq_one (5763 : ZMod 11527)
      decide
    · apply IsUnit.of_mul_eq_one (5845 : ZMod 11527)
      decide
    · apply IsUnit.of_mul_eq_one (7186 : ZMod 11527)
      decide
    · apply IsUnit.of_mul_eq_one (10095 : ZMod 11527)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11549 : Nat.Prime 11549 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11549 11548 1 2 [2, 2, 2887]
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
    · apply IsUnit.of_mul_eq_one (5774 : ZMod 11549)
      decide
    · apply IsUnit.of_mul_eq_one (770 : ZMod 11549)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11551 : Nat.Prime 11551 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11551 11550 1 7 [2, 3, 5, 5, 7, 11]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5775 : ZMod 11551)
      decide
    · apply IsUnit.of_mul_eq_one (1326 : ZMod 11551)
      decide
    · apply IsUnit.of_mul_eq_one (268 : ZMod 11551)
      decide
    · apply IsUnit.of_mul_eq_one (5175 : ZMod 11551)
      decide
    · apply IsUnit.of_mul_eq_one (8688 : ZMod 11551)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11579 : Nat.Prime 11579 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11579 11578 1 2 [2, 7, 827]
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
    · apply IsUnit.of_mul_eq_one (5789 : ZMod 11579)
      decide
    · apply IsUnit.of_mul_eq_one (8101 : ZMod 11579)
      decide
    · apply IsUnit.of_mul_eq_one (2297 : ZMod 11579)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11587 : Nat.Prime 11587 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11587 11586 1 2 [2, 3, 1931]
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
    · apply IsUnit.of_mul_eq_one (5793 : ZMod 11587)
      decide
    · apply IsUnit.of_mul_eq_one (4113 : ZMod 11587)
      decide
    · apply IsUnit.of_mul_eq_one (6989 : ZMod 11587)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11593 : Nat.Prime 11593 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11593 11592 1 5 [2, 2, 2, 3, 3, 7, 23]
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
    · apply IsUnit.of_mul_eq_one (5796 : ZMod 11593)
      decide
    · apply IsUnit.of_mul_eq_one (4421 : ZMod 11593)
      decide
    · apply IsUnit.of_mul_eq_one (2865 : ZMod 11593)
      decide
    · apply IsUnit.of_mul_eq_one (2459 : ZMod 11593)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11597 : Nat.Prime 11597 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11597 11596 1 3 [2, 2, 13, 223]
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
    · apply IsUnit.of_mul_eq_one (5798 : ZMod 11597)
      decide
    · apply IsUnit.of_mul_eq_one (7395 : ZMod 11597)
      decide
    · apply IsUnit.of_mul_eq_one (5676 : ZMod 11597)
      decide
  · norm_num

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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11701 : Nat.Prime 11701 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11701 11700 1 6 [2, 2, 3, 3, 5, 5, 13]
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
    · apply IsUnit.of_mul_eq_one (5850 : ZMod 11701)
      decide
    · apply IsUnit.of_mul_eq_one (10348 : ZMod 11701)
      decide
    · apply IsUnit.of_mul_eq_one (3104 : ZMod 11701)
      decide
    · apply IsUnit.of_mul_eq_one (6040 : ZMod 11701)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11717 : Nat.Prime 11717 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11717 11716 1 2 [2, 2, 29, 101]
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
    · apply IsUnit.of_mul_eq_one (5858 : ZMod 11717)
      decide
    · apply IsUnit.of_mul_eq_one (4268 : ZMod 11717)
      decide
    · apply IsUnit.of_mul_eq_one (1290 : ZMod 11717)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11719 : Nat.Prime 11719 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11719 11718 1 6 [2, 3, 3, 3, 7, 31]
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
    · apply IsUnit.of_mul_eq_one (5859 : ZMod 11719)
      decide
    · apply IsUnit.of_mul_eq_one (11656 : ZMod 11719)
      decide
    · apply IsUnit.of_mul_eq_one (8211 : ZMod 11719)
      decide
    · apply IsUnit.of_mul_eq_one (3272 : ZMod 11719)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11731 : Nat.Prime 11731 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11731 11730 1 3 [2, 3, 5, 17, 23]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5865 : ZMod 11731)
      decide
    · apply IsUnit.of_mul_eq_one (6694 : ZMod 11731)
      decide
    · apply IsUnit.of_mul_eq_one (997 : ZMod 11731)
      decide
    · apply IsUnit.of_mul_eq_one (2554 : ZMod 11731)
      decide
    · apply IsUnit.of_mul_eq_one (7388 : ZMod 11731)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11743 : Nat.Prime 11743 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11743 11742 1 3 [2, 3, 19, 103]
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
    · apply IsUnit.of_mul_eq_one (5871 : ZMod 11743)
      decide
    · apply IsUnit.of_mul_eq_one (10690 : ZMod 11743)
      decide
    · apply IsUnit.of_mul_eq_one (2940 : ZMod 11743)
      decide
    · apply IsUnit.of_mul_eq_one (7133 : ZMod 11743)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11777 : Nat.Prime 11777 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11777 11776 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 23]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (5888 : ZMod 11777)
      decide
    · apply IsUnit.of_mul_eq_one (6100 : ZMod 11777)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11779 : Nat.Prime 11779 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11779 11778 1 2 [2, 3, 13, 151]
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
    · apply IsUnit.of_mul_eq_one (5889 : ZMod 11779)
      decide
    · apply IsUnit.of_mul_eq_one (9173 : ZMod 11779)
      decide
    · apply IsUnit.of_mul_eq_one (4971 : ZMod 11779)
      decide
    · apply IsUnit.of_mul_eq_one (10790 : ZMod 11779)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11783 : Nat.Prime 11783 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11783 11782 1 5 [2, 43, 137]
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
    · apply IsUnit.of_mul_eq_one (5891 : ZMod 11783)
      decide
    · apply IsUnit.of_mul_eq_one (11540 : ZMod 11783)
      decide
    · apply IsUnit.of_mul_eq_one (10809 : ZMod 11783)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11789 : Nat.Prime 11789 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11789 11788 1 2 [2, 2, 7, 421]
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
    · apply IsUnit.of_mul_eq_one (5894 : ZMod 11789)
      decide
    · apply IsUnit.of_mul_eq_one (1837 : ZMod 11789)
      decide
    · apply IsUnit.of_mul_eq_one (9274 : ZMod 11789)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11801 : Nat.Prime 11801 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11801 11800 1 3 [2, 2, 2, 5, 5, 59]
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
    · apply IsUnit.of_mul_eq_one (5900 : ZMod 11801)
      decide
    · apply IsUnit.of_mul_eq_one (51 : ZMod 11801)
      decide
    · apply IsUnit.of_mul_eq_one (3077 : ZMod 11801)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11807 : Nat.Prime 11807 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11807 11806 1 5 [2, 5903]
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
    · apply IsUnit.of_mul_eq_one (5903 : ZMod 11807)
      decide
    · apply IsUnit.of_mul_eq_one (492 : ZMod 11807)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11813 : Nat.Prime 11813 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11813 11812 1 2 [2, 2, 2953]
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
    · apply IsUnit.of_mul_eq_one (5906 : ZMod 11813)
      decide
    · apply IsUnit.of_mul_eq_one (10238 : ZMod 11813)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11821 : Nat.Prime 11821 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11821 11820 1 2 [2, 2, 3, 5, 197]
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
    · apply IsUnit.of_mul_eq_one (5910 : ZMod 11821)
      decide
    · apply IsUnit.of_mul_eq_one (11471 : ZMod 11821)
      decide
    · apply IsUnit.of_mul_eq_one (1566 : ZMod 11821)
      decide
    · apply IsUnit.of_mul_eq_one (2941 : ZMod 11821)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11827 : Nat.Prime 11827 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11827 11826 1 2 [2, 3, 3, 3, 3, 73]
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
    · apply IsUnit.of_mul_eq_one (5913 : ZMod 11827)
      decide
    · apply IsUnit.of_mul_eq_one (9131 : ZMod 11827)
      decide
    · apply IsUnit.of_mul_eq_one (3225 : ZMod 11827)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11831 : Nat.Prime 11831 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11831 11830 1 7 [2, 5, 7, 13, 13]
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
    · apply IsUnit.of_mul_eq_one (5915 : ZMod 11831)
      decide
    · apply IsUnit.of_mul_eq_one (3558 : ZMod 11831)
      decide
    · apply IsUnit.of_mul_eq_one (3933 : ZMod 11831)
      decide
    · apply IsUnit.of_mul_eq_one (3417 : ZMod 11831)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11833 : Nat.Prime 11833 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11833 11832 1 5 [2, 2, 2, 3, 17, 29]
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
    · apply IsUnit.of_mul_eq_one (5916 : ZMod 11833)
      decide
    · apply IsUnit.of_mul_eq_one (872 : ZMod 11833)
      decide
    · apply IsUnit.of_mul_eq_one (11138 : ZMod 11833)
      decide
    · apply IsUnit.of_mul_eq_one (11064 : ZMod 11833)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11839 : Nat.Prime 11839 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11839 11838 1 3 [2, 3, 1973]
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
    · apply IsUnit.of_mul_eq_one (5919 : ZMod 11839)
      decide
    · apply IsUnit.of_mul_eq_one (11612 : ZMod 11839)
      decide
    · apply IsUnit.of_mul_eq_one (7562 : ZMod 11839)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11863 : Nat.Prime 11863 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11863 11862 1 3 [2, 3, 3, 659]
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
    · apply IsUnit.of_mul_eq_one (5931 : ZMod 11863)
      decide
    · apply IsUnit.of_mul_eq_one (5029 : ZMod 11863)
      decide
    · apply IsUnit.of_mul_eq_one (3413 : ZMod 11863)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11867 : Nat.Prime 11867 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11867 11866 1 2 [2, 17, 349]
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
    · apply IsUnit.of_mul_eq_one (5933 : ZMod 11867)
      decide
    · apply IsUnit.of_mul_eq_one (9315 : ZMod 11867)
      decide
    · apply IsUnit.of_mul_eq_one (10568 : ZMod 11867)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11887 : Nat.Prime 11887 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11887 11886 1 3 [2, 3, 7, 283]
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
    · apply IsUnit.of_mul_eq_one (5943 : ZMod 11887)
      decide
    · apply IsUnit.of_mul_eq_one (5473 : ZMod 11887)
      decide
    · apply IsUnit.of_mul_eq_one (5365 : ZMod 11887)
      decide
    · apply IsUnit.of_mul_eq_one (8152 : ZMod 11887)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11897 : Nat.Prime 11897 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11897 11896 1 3 [2, 2, 2, 1487]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (5948 : ZMod 11897)
      decide
    · apply IsUnit.of_mul_eq_one (3930 : ZMod 11897)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11903 : Nat.Prime 11903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11903 11902 1 5 [2, 11, 541]
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
    · apply IsUnit.of_mul_eq_one (5951 : ZMod 11903)
      decide
    · apply IsUnit.of_mul_eq_one (5835 : ZMod 11903)
      decide
    · apply IsUnit.of_mul_eq_one (9109 : ZMod 11903)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11909 : Nat.Prime 11909 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11909 11908 1 2 [2, 2, 13, 229]
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
    · apply IsUnit.of_mul_eq_one (5954 : ZMod 11909)
      decide
    · apply IsUnit.of_mul_eq_one (7002 : ZMod 11909)
      decide
    · apply IsUnit.of_mul_eq_one (7695 : ZMod 11909)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11923 : Nat.Prime 11923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11923 11922 1 5 [2, 3, 1987]
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
    · apply IsUnit.of_mul_eq_one (5961 : ZMod 11923)
      decide
    · apply IsUnit.of_mul_eq_one (10440 : ZMod 11923)
      decide
    · apply IsUnit.of_mul_eq_one (3795 : ZMod 11923)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11927 : Nat.Prime 11927 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11927 11926 1 5 [2, 67, 89]
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
    · apply IsUnit.of_mul_eq_one (5963 : ZMod 11927)
      decide
    · apply IsUnit.of_mul_eq_one (5850 : ZMod 11927)
      decide
    · apply IsUnit.of_mul_eq_one (10316 : ZMod 11927)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11933 : Nat.Prime 11933 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11933 11932 1 2 [2, 2, 19, 157]
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
    · apply IsUnit.of_mul_eq_one (5966 : ZMod 11933)
      decide
    · apply IsUnit.of_mul_eq_one (10542 : ZMod 11933)
      decide
    · apply IsUnit.of_mul_eq_one (3072 : ZMod 11933)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11939 : Nat.Prime 11939 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11939 11938 1 2 [2, 47, 127]
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
    · apply IsUnit.of_mul_eq_one (5969 : ZMod 11939)
      decide
    · apply IsUnit.of_mul_eq_one (6685 : ZMod 11939)
      decide
    · apply IsUnit.of_mul_eq_one (440 : ZMod 11939)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11941 : Nat.Prime 11941 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11941 11940 1 10 [2, 2, 3, 5, 199]
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
    · apply IsUnit.of_mul_eq_one (5970 : ZMod 11941)
      decide
    · apply IsUnit.of_mul_eq_one (9024 : ZMod 11941)
      decide
    · apply IsUnit.of_mul_eq_one (5174 : ZMod 11941)
      decide
    · apply IsUnit.of_mul_eq_one (9848 : ZMod 11941)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11953 : Nat.Prime 11953 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11953 11952 1 5 [2, 2, 2, 2, 3, 3, 83]
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
    · apply IsUnit.of_mul_eq_one (5976 : ZMod 11953)
      decide
    · apply IsUnit.of_mul_eq_one (9006 : ZMod 11953)
      decide
    · apply IsUnit.of_mul_eq_one (4077 : ZMod 11953)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11959 : Nat.Prime 11959 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11959 11958 1 3 [2, 3, 1993]
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
    · apply IsUnit.of_mul_eq_one (5979 : ZMod 11959)
      decide
    · apply IsUnit.of_mul_eq_one (7717 : ZMod 11959)
      decide
    · apply IsUnit.of_mul_eq_one (10267 : ZMod 11959)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11969 : Nat.Prime 11969 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11969 11968 1 3 [2, 2, 2, 2, 2, 2, 11, 17]
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
    · apply IsUnit.of_mul_eq_one (5984 : ZMod 11969)
      decide
    · apply IsUnit.of_mul_eq_one (4751 : ZMod 11969)
      decide
    · apply IsUnit.of_mul_eq_one (8177 : ZMod 11969)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11971 : Nat.Prime 11971 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11971 11970 1 10 [2, 3, 3, 5, 7, 19]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5985 : ZMod 11971)
      decide
    · apply IsUnit.of_mul_eq_one (9722 : ZMod 11971)
      decide
    · apply IsUnit.of_mul_eq_one (10508 : ZMod 11971)
      decide
    · apply IsUnit.of_mul_eq_one (3312 : ZMod 11971)
      decide
    · apply IsUnit.of_mul_eq_one (5504 : ZMod 11971)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11981 : Nat.Prime 11981 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11981 11980 1 2 [2, 2, 5, 599]
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
    · apply IsUnit.of_mul_eq_one (5990 : ZMod 11981)
      decide
    · apply IsUnit.of_mul_eq_one (2157 : ZMod 11981)
      decide
    · apply IsUnit.of_mul_eq_one (5877 : ZMod 11981)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11987 : Nat.Prime 11987 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11987 11986 1 2 [2, 13, 461]
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
    · apply IsUnit.of_mul_eq_one (5993 : ZMod 11987)
      decide
    · apply IsUnit.of_mul_eq_one (3607 : ZMod 11987)
      decide
    · apply IsUnit.of_mul_eq_one (9482 : ZMod 11987)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12007 : Nat.Prime 12007 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12007 12006 1 13 [2, 3, 3, 23, 29]
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
    · apply IsUnit.of_mul_eq_one (6003 : ZMod 12007)
      decide
    · apply IsUnit.of_mul_eq_one (11403 : ZMod 12007)
      decide
    · apply IsUnit.of_mul_eq_one (9904 : ZMod 12007)
      decide
    · apply IsUnit.of_mul_eq_one (11898 : ZMod 12007)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12011 : Nat.Prime 12011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12011 12010 1 2 [2, 5, 1201]
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
    · apply IsUnit.of_mul_eq_one (6005 : ZMod 12011)
      decide
    · apply IsUnit.of_mul_eq_one (1640 : ZMod 12011)
      decide
    · apply IsUnit.of_mul_eq_one (1949 : ZMod 12011)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12037 : Nat.Prime 12037 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12037 12036 1 5 [2, 2, 3, 17, 59]
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
    · apply IsUnit.of_mul_eq_one (6018 : ZMod 12037)
      decide
    · apply IsUnit.of_mul_eq_one (4443 : ZMod 12037)
      decide
    · apply IsUnit.of_mul_eq_one (3487 : ZMod 12037)
      decide
    · apply IsUnit.of_mul_eq_one (7037 : ZMod 12037)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12041 : Nat.Prime 12041 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12041 12040 1 3 [2, 2, 2, 5, 7, 43]
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
    · apply IsUnit.of_mul_eq_one (6020 : ZMod 12041)
      decide
    · apply IsUnit.of_mul_eq_one (1005 : ZMod 12041)
      decide
    · apply IsUnit.of_mul_eq_one (1759 : ZMod 12041)
      decide
    · apply IsUnit.of_mul_eq_one (7076 : ZMod 12041)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12043 : Nat.Prime 12043 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12043 12042 1 2 [2, 3, 3, 3, 223]
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
    · apply IsUnit.of_mul_eq_one (6021 : ZMod 12043)
      decide
    · apply IsUnit.of_mul_eq_one (1054 : ZMod 12043)
      decide
    · apply IsUnit.of_mul_eq_one (230 : ZMod 12043)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12049 : Nat.Prime 12049 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12049 12048 1 13 [2, 2, 2, 2, 3, 251]
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
    · apply IsUnit.of_mul_eq_one (6024 : ZMod 12049)
      decide
    · apply IsUnit.of_mul_eq_one (11820 : ZMod 12049)
      decide
    · apply IsUnit.of_mul_eq_one (11284 : ZMod 12049)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12071 : Nat.Prime 12071 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12071 12070 1 11 [2, 5, 17, 71]
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
    · apply IsUnit.of_mul_eq_one (6035 : ZMod 12071)
      decide
    · apply IsUnit.of_mul_eq_one (11856 : ZMod 12071)
      decide
    · apply IsUnit.of_mul_eq_one (3067 : ZMod 12071)
      decide
    · apply IsUnit.of_mul_eq_one (6470 : ZMod 12071)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12073 : Nat.Prime 12073 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12073 12072 1 7 [2, 2, 2, 3, 503]
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
    · apply IsUnit.of_mul_eq_one (6036 : ZMod 12073)
      decide
    · apply IsUnit.of_mul_eq_one (8805 : ZMod 12073)
      decide
    · apply IsUnit.of_mul_eq_one (11308 : ZMod 12073)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12097 : Nat.Prime 12097 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12097 12096 1 5 [2, 2, 2, 2, 2, 2, 3, 3, 3, 7]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6048 : ZMod 12097)
      decide
    · apply IsUnit.of_mul_eq_one (12033 : ZMod 12097)
      decide
    · apply IsUnit.of_mul_eq_one (7462 : ZMod 12097)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12101 : Nat.Prime 12101 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12101 12100 1 3 [2, 2, 5, 5, 11, 11]
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
    · apply IsUnit.of_mul_eq_one (6050 : ZMod 12101)
      decide
    · apply IsUnit.of_mul_eq_one (2814 : ZMod 12101)
      decide
    · apply IsUnit.of_mul_eq_one (8398 : ZMod 12101)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12107 : Nat.Prime 12107 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12107 12106 1 2 [2, 6053]
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
    · apply IsUnit.of_mul_eq_one (6053 : ZMod 12107)
      decide
    · apply IsUnit.of_mul_eq_one (4036 : ZMod 12107)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12109 : Nat.Prime 12109 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12109 12108 1 6 [2, 2, 3, 1009]
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
    · apply IsUnit.of_mul_eq_one (6054 : ZMod 12109)
      decide
    · apply IsUnit.of_mul_eq_one (6928 : ZMod 12109)
      decide
    · apply IsUnit.of_mul_eq_one (2073 : ZMod 12109)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12113 : Nat.Prime 12113 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12113 12112 1 3 [2, 2, 2, 2, 757]
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
    · apply IsUnit.of_mul_eq_one (6056 : ZMod 12113)
      decide
    · apply IsUnit.of_mul_eq_one (10705 : ZMod 12113)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12119 : Nat.Prime 12119 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12119 12118 1 7 [2, 73, 83]
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
    · apply IsUnit.of_mul_eq_one (6059 : ZMod 12119)
      decide
    · apply IsUnit.of_mul_eq_one (8518 : ZMod 12119)
      decide
    · apply IsUnit.of_mul_eq_one (4857 : ZMod 12119)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12143 : Nat.Prime 12143 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12143 12142 1 10 [2, 13, 467]
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
    · apply IsUnit.of_mul_eq_one (6071 : ZMod 12143)
      decide
    · apply IsUnit.of_mul_eq_one (6061 : ZMod 12143)
      decide
    · apply IsUnit.of_mul_eq_one (8659 : ZMod 12143)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12149 : Nat.Prime 12149 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12149 12148 1 2 [2, 2, 3037]
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
    · apply IsUnit.of_mul_eq_one (6074 : ZMod 12149)
      decide
    · apply IsUnit.of_mul_eq_one (810 : ZMod 12149)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12157 : Nat.Prime 12157 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12157 12156 1 2 [2, 2, 3, 1013]
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
    · apply IsUnit.of_mul_eq_one (6078 : ZMod 12157)
      decide
    · apply IsUnit.of_mul_eq_one (2189 : ZMod 12157)
      decide
    · apply IsUnit.of_mul_eq_one (95 : ZMod 12157)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12161 : Nat.Prime 12161 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12161 12160 1 3 [2, 2, 2, 2, 2, 2, 2, 5, 19]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6080 : ZMod 12161)
      decide
    · apply IsUnit.of_mul_eq_one (7780 : ZMod 12161)
      decide
    · apply IsUnit.of_mul_eq_one (3195 : ZMod 12161)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12163 : Nat.Prime 12163 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12163 12162 1 5 [2, 3, 2027]
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
    · apply IsUnit.of_mul_eq_one (6081 : ZMod 12163)
      decide
    · apply IsUnit.of_mul_eq_one (1898 : ZMod 12163)
      decide
    · apply IsUnit.of_mul_eq_one (6020 : ZMod 12163)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12197 : Nat.Prime 12197 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12197 12196 1 2 [2, 2, 3049]
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
    · apply IsUnit.of_mul_eq_one (6098 : ZMod 12197)
      decide
    · apply IsUnit.of_mul_eq_one (5692 : ZMod 12197)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12203 : Nat.Prime 12203 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12203 12202 1 2 [2, 6101]
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
    · apply IsUnit.of_mul_eq_one (6101 : ZMod 12203)
      decide
    · apply IsUnit.of_mul_eq_one (4068 : ZMod 12203)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12211 : Nat.Prime 12211 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12211 12210 1 2 [2, 3, 5, 11, 37]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6105 : ZMod 12211)
      decide
    · apply IsUnit.of_mul_eq_one (8177 : ZMod 12211)
      decide
    · apply IsUnit.of_mul_eq_one (11902 : ZMod 12211)
      decide
    · apply IsUnit.of_mul_eq_one (5157 : ZMod 12211)
      decide
    · apply IsUnit.of_mul_eq_one (10572 : ZMod 12211)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12227 : Nat.Prime 12227 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12227 12226 1 2 [2, 6113]
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
    · apply IsUnit.of_mul_eq_one (6113 : ZMod 12227)
      decide
    · apply IsUnit.of_mul_eq_one (4076 : ZMod 12227)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12239 : Nat.Prime 12239 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12239 12238 1 13 [2, 29, 211]
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
    · apply IsUnit.of_mul_eq_one (6119 : ZMod 12239)
      decide
    · apply IsUnit.of_mul_eq_one (11871 : ZMod 12239)
      decide
    · apply IsUnit.of_mul_eq_one (1115 : ZMod 12239)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12241 : Nat.Prime 12241 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12241 12240 1 7 [2, 2, 2, 2, 3, 3, 5, 17]
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
    · apply IsUnit.of_mul_eq_one (6120 : ZMod 12241)
      decide
    · apply IsUnit.of_mul_eq_one (3102 : ZMod 12241)
      decide
    · apply IsUnit.of_mul_eq_one (6232 : ZMod 12241)
      decide
    · apply IsUnit.of_mul_eq_one (10055 : ZMod 12241)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12251 : Nat.Prime 12251 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12251 12250 1 2 [2, 5, 5, 5, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (6125 : ZMod 12251)
      decide
    · apply IsUnit.of_mul_eq_one (864 : ZMod 12251)
      decide
    · apply IsUnit.of_mul_eq_one (343 : ZMod 12251)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12253 : Nat.Prime 12253 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12253 12252 1 2 [2, 2, 3, 1021]
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
    · apply IsUnit.of_mul_eq_one (6126 : ZMod 12253)
      decide
    · apply IsUnit.of_mul_eq_one (3923 : ZMod 12253)
      decide
    · apply IsUnit.of_mul_eq_one (383 : ZMod 12253)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12263 : Nat.Prime 12263 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12263 12262 1 5 [2, 6131]
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
    · apply IsUnit.of_mul_eq_one (6131 : ZMod 12263)
      decide
    · apply IsUnit.of_mul_eq_one (511 : ZMod 12263)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12269 : Nat.Prime 12269 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12269 12268 1 2 [2, 2, 3067]
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
    · apply IsUnit.of_mul_eq_one (6134 : ZMod 12269)
      decide
    · apply IsUnit.of_mul_eq_one (818 : ZMod 12269)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12277 : Nat.Prime 12277 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12277 12276 1 2 [2, 2, 3, 3, 11, 31]
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
    · apply IsUnit.of_mul_eq_one (6138 : ZMod 12277)
      decide
    · apply IsUnit.of_mul_eq_one (4225 : ZMod 12277)
      decide
    · apply IsUnit.of_mul_eq_one (9211 : ZMod 12277)
      decide
    · apply IsUnit.of_mul_eq_one (11559 : ZMod 12277)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12281 : Nat.Prime 12281 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12281 12280 1 3 [2, 2, 2, 5, 307]
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
    · apply IsUnit.of_mul_eq_one (6140 : ZMod 12281)
      decide
    · apply IsUnit.of_mul_eq_one (9872 : ZMod 12281)
      decide
    · apply IsUnit.of_mul_eq_one (11008 : ZMod 12281)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12289 : Nat.Prime 12289 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12289 12288 1 11 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6144 : ZMod 12289)
      decide
    · apply IsUnit.of_mul_eq_one (6112 : ZMod 12289)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12301 : Nat.Prime 12301 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12301 12300 1 2 [2, 2, 3, 5, 5, 41]
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
    · apply IsUnit.of_mul_eq_one (6150 : ZMod 12301)
      decide
    · apply IsUnit.of_mul_eq_one (4842 : ZMod 12301)
      decide
    · apply IsUnit.of_mul_eq_one (11127 : ZMod 12301)
      decide
    · apply IsUnit.of_mul_eq_one (4046 : ZMod 12301)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12323 : Nat.Prime 12323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12323 12322 1 2 [2, 61, 101]
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
    · apply IsUnit.of_mul_eq_one (6161 : ZMod 12323)
      decide
    · apply IsUnit.of_mul_eq_one (5544 : ZMod 12323)
      decide
    · apply IsUnit.of_mul_eq_one (7108 : ZMod 12323)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12329 : Nat.Prime 12329 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12329 12328 1 3 [2, 2, 2, 23, 67]
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
    · apply IsUnit.of_mul_eq_one (6164 : ZMod 12329)
      decide
    · apply IsUnit.of_mul_eq_one (5546 : ZMod 12329)
      decide
    · apply IsUnit.of_mul_eq_one (4919 : ZMod 12329)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12343 : Nat.Prime 12343 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12343 12342 1 7 [2, 3, 11, 11, 17]
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
    · apply IsUnit.of_mul_eq_one (6171 : ZMod 12343)
      decide
    · apply IsUnit.of_mul_eq_one (2973 : ZMod 12343)
      decide
    · apply IsUnit.of_mul_eq_one (329 : ZMod 12343)
      decide
    · apply IsUnit.of_mul_eq_one (10564 : ZMod 12343)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12347 : Nat.Prime 12347 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12347 12346 1 2 [2, 6173]
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
    · apply IsUnit.of_mul_eq_one (6173 : ZMod 12347)
      decide
    · apply IsUnit.of_mul_eq_one (4116 : ZMod 12347)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12373 : Nat.Prime 12373 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12373 12372 1 2 [2, 2, 3, 1031]
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
    · apply IsUnit.of_mul_eq_one (6186 : ZMod 12373)
      decide
    · apply IsUnit.of_mul_eq_one (3625 : ZMod 12373)
      decide
    · apply IsUnit.of_mul_eq_one (2109 : ZMod 12373)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12377 : Nat.Prime 12377 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12377 12376 1 6 [2, 2, 2, 7, 13, 17]
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
    · apply IsUnit.of_mul_eq_one (6188 : ZMod 12377)
      decide
    · apply IsUnit.of_mul_eq_one (8825 : ZMod 12377)
      decide
    · apply IsUnit.of_mul_eq_one (6991 : ZMod 12377)
      decide
    · apply IsUnit.of_mul_eq_one (11353 : ZMod 12377)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12379 : Nat.Prime 12379 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12379 12378 1 2 [2, 3, 2063]
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
    · apply IsUnit.of_mul_eq_one (6189 : ZMod 12379)
      decide
    · apply IsUnit.of_mul_eq_one (6329 : ZMod 12379)
      decide
    · apply IsUnit.of_mul_eq_one (393 : ZMod 12379)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12391 : Nat.Prime 12391 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12391 12390 1 26 [2, 3, 5, 7, 59]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6195 : ZMod 12391)
      decide
    · apply IsUnit.of_mul_eq_one (1409 : ZMod 12391)
      decide
    · apply IsUnit.of_mul_eq_one (953 : ZMod 12391)
      decide
    · apply IsUnit.of_mul_eq_one (956 : ZMod 12391)
      decide
    · apply IsUnit.of_mul_eq_one (8506 : ZMod 12391)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11503) (q := 11519) (by exact lowPrime_11519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11519) (q := 11527) (by exact lowPrime_11527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11527) (q := 11549) (by exact lowPrime_11549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11549) (q := 11551) (by exact lowPrime_11551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11551) (q := 11579) (by exact lowPrime_11579) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11579) (q := 11587) (by exact lowPrime_11587) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11587) (q := 11593) (by exact lowPrime_11593) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11593) (q := 11597) (by exact lowPrime_11597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part01_chain :
    DusartPrimeRowsChain 11503 11596 dusartPrimeRows_11503_12096_part01 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11699) (q := 11701) (by exact lowPrime_11701) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11701) (q := 11717) (by exact lowPrime_11717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11717) (q := 11719) (by exact lowPrime_11719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11719) (q := 11731) (by exact lowPrime_11731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11731) (q := 11743) (by exact lowPrime_11743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11743) (q := 11777) (by exact lowPrime_11777) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11777) (q := 11779) (by exact lowPrime_11779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11779) (q := 11783) (by exact lowPrime_11783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part03_chain :
    DusartPrimeRowsChain 11699 11782 dusartPrimeRows_11503_12096_part03 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11783) (q := 11789) (by exact lowPrime_11789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11789) (q := 11801) (by exact lowPrime_11801) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11801) (q := 11807) (by exact lowPrime_11807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11807) (q := 11813) (by exact lowPrime_11813) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11813) (q := 11821) (by exact lowPrime_11821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11821) (q := 11827) (by exact lowPrime_11827) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11827) (q := 11831) (by exact lowPrime_11831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11831) (q := 11833) (by exact lowPrime_11833) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part04_chain :
    DusartPrimeRowsChain 11783 11832 dusartPrimeRows_11503_12096_part04 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11833) (q := 11839) (by exact lowPrime_11839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11839) (q := 11863) (by exact lowPrime_11863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11863) (q := 11867) (by exact lowPrime_11867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11867) (q := 11887) (by exact lowPrime_11887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11887) (q := 11897) (by exact lowPrime_11897) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11897) (q := 11903) (by exact lowPrime_11903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11903) (q := 11909) (by exact lowPrime_11909) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11909) (q := 11923) (by exact lowPrime_11923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part05_chain :
    DusartPrimeRowsChain 11833 11922 dusartPrimeRows_11503_12096_part05 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11923) (q := 11927) (by exact lowPrime_11927) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11927) (q := 11933) (by exact lowPrime_11933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11933) (q := 11939) (by exact lowPrime_11939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11939) (q := 11941) (by exact lowPrime_11941) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11941) (q := 11953) (by exact lowPrime_11953) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11953) (q := 11959) (by exact lowPrime_11959) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11959) (q := 11969) (by exact lowPrime_11969) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11969) (q := 11971) (by exact lowPrime_11971) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part06_chain :
    DusartPrimeRowsChain 11923 11970 dusartPrimeRows_11503_12096_part06 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11971) (q := 11981) (by exact lowPrime_11981) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11981) (q := 11987) (by exact lowPrime_11987) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11987) (q := 12007) (by exact lowPrime_12007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12007) (q := 12011) (by exact lowPrime_12011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12011) (q := 12037) (by exact lowPrime_12037) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12037) (q := 12041) (by exact lowPrime_12041) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12041) (q := 12043) (by exact lowPrime_12043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12043) (q := 12049) (by exact lowPrime_12049) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part07_chain :
    DusartPrimeRowsChain 11971 12048 dusartPrimeRows_11503_12096_part07 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 12049) (q := 12071) (by exact lowPrime_12071) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12071) (q := 12073) (by exact lowPrime_12073) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12073) (q := 12097) (by exact lowPrime_12097) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part08_chain :
    DusartPrimeRowsChain 12049 12096 dusartPrimeRows_11503_12096_part08 := by
  apply DusartPrimeRowsChain.cons
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12097) (q := 12101) (by exact lowPrime_12101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12101) (q := 12107) (by exact lowPrime_12107) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12107) (q := 12109) (by exact lowPrime_12109) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12109) (q := 12113) (by exact lowPrime_12113) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12113) (q := 12119) (by exact lowPrime_12119) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12119) (q := 12143) (by exact lowPrime_12143) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12143) (q := 12149) (by exact lowPrime_12149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12149) (q := 12157) (by exact lowPrime_12157) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part01_chain :
    DusartPrimeRowsChain 12097 12156 dusartPrimeRows_12097_12712_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12157) (q := 12161) (by exact lowPrime_12161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12161) (q := 12163) (by exact lowPrime_12163) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12163) (q := 12197) (by exact lowPrime_12197) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12197) (q := 12203) (by exact lowPrime_12203) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12203) (q := 12211) (by exact lowPrime_12211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12211) (q := 12227) (by exact lowPrime_12227) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12227) (q := 12239) (by exact lowPrime_12239) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12239) (q := 12241) (by exact lowPrime_12241) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part02_chain :
    DusartPrimeRowsChain 12157 12240 dusartPrimeRows_12097_12712_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12241) (q := 12251) (by exact lowPrime_12251) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12251) (q := 12253) (by exact lowPrime_12253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12253) (q := 12263) (by exact lowPrime_12263) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12263) (q := 12269) (by exact lowPrime_12269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12269) (q := 12277) (by exact lowPrime_12277) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12277) (q := 12281) (by exact lowPrime_12281) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12281) (q := 12289) (by exact lowPrime_12289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12289) (q := 12301) (by exact lowPrime_12301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part03_chain :
    DusartPrimeRowsChain 12241 12300 dusartPrimeRows_12097_12712_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12301) (q := 12323) (by exact lowPrime_12323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12323) (q := 12329) (by exact lowPrime_12329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12329) (q := 12343) (by exact lowPrime_12343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12343) (q := 12347) (by exact lowPrime_12347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12347) (q := 12373) (by exact lowPrime_12373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12373) (q := 12377) (by exact lowPrime_12377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12377) (q := 12379) (by exact lowPrime_12379) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12379) (q := 12391) (by exact lowPrime_12391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part04_chain :
    DusartPrimeRowsChain 12301 12390 dusartPrimeRows_12097_12712_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]
