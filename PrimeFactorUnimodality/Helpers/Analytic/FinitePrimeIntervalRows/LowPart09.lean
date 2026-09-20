import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 09 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9781 : Nat.Prime 9781 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9781 9780 1 6 [2, 2, 3, 5, 163]
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
    · apply IsUnit.of_mul_eq_one (4890 : ZMod 9781)
      decide
    · apply IsUnit.of_mul_eq_one (1824 : ZMod 9781)
      decide
    · apply IsUnit.of_mul_eq_one (1602 : ZMod 9781)
      decide
    · apply IsUnit.of_mul_eq_one (1085 : ZMod 9781)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9787 : Nat.Prime 9787 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9787 9786 1 3 [2, 3, 7, 233]
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
    · apply IsUnit.of_mul_eq_one (4893 : ZMod 9787)
      decide
    · apply IsUnit.of_mul_eq_one (1010 : ZMod 9787)
      decide
    · apply IsUnit.of_mul_eq_one (4852 : ZMod 9787)
      decide
    · apply IsUnit.of_mul_eq_one (2923 : ZMod 9787)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9791 : Nat.Prime 9791 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9791 9790 1 11 [2, 5, 11, 89]
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
    · apply IsUnit.of_mul_eq_one (4895 : ZMod 9791)
      decide
    · apply IsUnit.of_mul_eq_one (2554 : ZMod 9791)
      decide
    · apply IsUnit.of_mul_eq_one (3431 : ZMod 9791)
      decide
    · apply IsUnit.of_mul_eq_one (1704 : ZMod 9791)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9803 : Nat.Prime 9803 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9803 9802 1 2 [2, 13, 13, 29]
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
    · apply IsUnit.of_mul_eq_one (4901 : ZMod 9803)
      decide
    · apply IsUnit.of_mul_eq_one (2966 : ZMod 9803)
      decide
    · apply IsUnit.of_mul_eq_one (5594 : ZMod 9803)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9811 : Nat.Prime 9811 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9811 9810 1 3 [2, 3, 3, 5, 109]
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
    · apply IsUnit.of_mul_eq_one (4905 : ZMod 9811)
      decide
    · apply IsUnit.of_mul_eq_one (6741 : ZMod 9811)
      decide
    · apply IsUnit.of_mul_eq_one (651 : ZMod 9811)
      decide
    · apply IsUnit.of_mul_eq_one (8430 : ZMod 9811)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9817 : Nat.Prime 9817 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9817 9816 1 5 [2, 2, 2, 3, 409]
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
    · apply IsUnit.of_mul_eq_one (4908 : ZMod 9817)
      decide
    · apply IsUnit.of_mul_eq_one (318 : ZMod 9817)
      decide
    · apply IsUnit.of_mul_eq_one (7256 : ZMod 9817)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9829 : Nat.Prime 9829 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9829 9828 1 10 [2, 2, 3, 3, 3, 7, 13]
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
    · apply IsUnit.of_mul_eq_one (4914 : ZMod 9829)
      decide
    · apply IsUnit.of_mul_eq_one (9579 : ZMod 9829)
      decide
    · apply IsUnit.of_mul_eq_one (7189 : ZMod 9829)
      decide
    · apply IsUnit.of_mul_eq_one (5419 : ZMod 9829)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9833 : Nat.Prime 9833 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9833 9832 1 3 [2, 2, 2, 1229]
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
    · apply IsUnit.of_mul_eq_one (4916 : ZMod 9833)
      decide
    · apply IsUnit.of_mul_eq_one (3512 : ZMod 9833)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9839 : Nat.Prime 9839 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9839 9838 1 7 [2, 4919]
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
    · apply IsUnit.of_mul_eq_one (4919 : ZMod 9839)
      decide
    · apply IsUnit.of_mul_eq_one (205 : ZMod 9839)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9851 : Nat.Prime 9851 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9851 9850 1 2 [2, 5, 5, 197]
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
    · apply IsUnit.of_mul_eq_one (4925 : ZMod 9851)
      decide
    · apply IsUnit.of_mul_eq_one (8629 : ZMod 9851)
      decide
    · apply IsUnit.of_mul_eq_one (3882 : ZMod 9851)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9857 : Nat.Prime 9857 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9857 9856 1 5 [2, 2, 2, 2, 2, 2, 2, 7, 11]
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
    · apply IsUnit.of_mul_eq_one (4928 : ZMod 9857)
      decide
    · apply IsUnit.of_mul_eq_one (19 : ZMod 9857)
      decide
    · apply IsUnit.of_mul_eq_one (1245 : ZMod 9857)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9859 : Nat.Prime 9859 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9859 9858 1 2 [2, 3, 31, 53]
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
    · apply IsUnit.of_mul_eq_one (4929 : ZMod 9859)
      decide
    · apply IsUnit.of_mul_eq_one (1583 : ZMod 9859)
      decide
    · apply IsUnit.of_mul_eq_one (3176 : ZMod 9859)
      decide
    · apply IsUnit.of_mul_eq_one (534 : ZMod 9859)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9871 : Nat.Prime 9871 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9871 9870 1 3 [2, 3, 5, 7, 47]
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
    · apply IsUnit.of_mul_eq_one (4935 : ZMod 9871)
      decide
    · apply IsUnit.of_mul_eq_one (3507 : ZMod 9871)
      decide
    · apply IsUnit.of_mul_eq_one (3318 : ZMod 9871)
      decide
    · apply IsUnit.of_mul_eq_one (6932 : ZMod 9871)
      decide
    · apply IsUnit.of_mul_eq_one (5909 : ZMod 9871)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9883 : Nat.Prime 9883 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9883 9882 1 2 [2, 3, 3, 3, 3, 61]
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
    · apply IsUnit.of_mul_eq_one (4941 : ZMod 9883)
      decide
    · apply IsUnit.of_mul_eq_one (9037 : ZMod 9883)
      decide
    · apply IsUnit.of_mul_eq_one (6434 : ZMod 9883)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9887 : Nat.Prime 9887 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9887 9886 1 5 [2, 4943]
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
    · apply IsUnit.of_mul_eq_one (4943 : ZMod 9887)
      decide
    · apply IsUnit.of_mul_eq_one (412 : ZMod 9887)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9901 : Nat.Prime 9901 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9901 9900 1 2 [2, 2, 3, 3, 5, 5, 11]
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
    · apply IsUnit.of_mul_eq_one (4950 : ZMod 9901)
      decide
    · apply IsUnit.of_mul_eq_one (6567 : ZMod 9901)
      decide
    · apply IsUnit.of_mul_eq_one (4084 : ZMod 9901)
      decide
    · apply IsUnit.of_mul_eq_one (4839 : ZMod 9901)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9907 : Nat.Prime 9907 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9907 9906 1 2 [2, 3, 13, 127]
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
    · apply IsUnit.of_mul_eq_one (4953 : ZMod 9907)
      decide
    · apply IsUnit.of_mul_eq_one (2190 : ZMod 9907)
      decide
    · apply IsUnit.of_mul_eq_one (6085 : ZMod 9907)
      decide
    · apply IsUnit.of_mul_eq_one (8864 : ZMod 9907)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9923 : Nat.Prime 9923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9923 9922 1 2 [2, 11, 11, 41]
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
    · apply IsUnit.of_mul_eq_one (4961 : ZMod 9923)
      decide
    · apply IsUnit.of_mul_eq_one (236 : ZMod 9923)
      decide
    · apply IsUnit.of_mul_eq_one (5175 : ZMod 9923)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9929 : Nat.Prime 9929 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9929 9928 1 3 [2, 2, 2, 17, 73]
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
    · apply IsUnit.of_mul_eq_one (4964 : ZMod 9929)
      decide
    · apply IsUnit.of_mul_eq_one (5034 : ZMod 9929)
      decide
    · apply IsUnit.of_mul_eq_one (9317 : ZMod 9929)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9931 : Nat.Prime 9931 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9931 9930 1 10 [2, 3, 5, 331]
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
    · apply IsUnit.of_mul_eq_one (4965 : ZMod 9931)
      decide
    · apply IsUnit.of_mul_eq_one (8520 : ZMod 9931)
      decide
    · apply IsUnit.of_mul_eq_one (4557 : ZMod 9931)
      decide
    · apply IsUnit.of_mul_eq_one (8867 : ZMod 9931)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9941 : Nat.Prime 9941 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9941 9940 1 2 [2, 2, 5, 7, 71]
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
    · apply IsUnit.of_mul_eq_one (4970 : ZMod 9941)
      decide
    · apply IsUnit.of_mul_eq_one (911 : ZMod 9941)
      decide
    · apply IsUnit.of_mul_eq_one (778 : ZMod 9941)
      decide
    · apply IsUnit.of_mul_eq_one (4064 : ZMod 9941)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9949 : Nat.Prime 9949 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9949 9948 1 2 [2, 2, 3, 829]
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
    · apply IsUnit.of_mul_eq_one (4974 : ZMod 9949)
      decide
    · apply IsUnit.of_mul_eq_one (5421 : ZMod 9949)
      decide
    · apply IsUnit.of_mul_eq_one (1776 : ZMod 9949)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9967 : Nat.Prime 9967 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9967 9966 1 3 [2, 3, 11, 151]
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
    · apply IsUnit.of_mul_eq_one (4983 : ZMod 9967)
      decide
    · apply IsUnit.of_mul_eq_one (152 : ZMod 9967)
      decide
    · apply IsUnit.of_mul_eq_one (9247 : ZMod 9967)
      decide
    · apply IsUnit.of_mul_eq_one (1834 : ZMod 9967)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9973 : Nat.Prime 9973 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9973 9972 1 11 [2, 2, 3, 3, 277]
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
    · apply IsUnit.of_mul_eq_one (4986 : ZMod 9973)
      decide
    · apply IsUnit.of_mul_eq_one (6125 : ZMod 9973)
      decide
    · apply IsUnit.of_mul_eq_one (891 : ZMod 9973)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10007 : Nat.Prime 10007 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10007 10006 1 5 [2, 5003]
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
    · apply IsUnit.of_mul_eq_one (5003 : ZMod 10007)
      decide
    · apply IsUnit.of_mul_eq_one (417 : ZMod 10007)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10009 : Nat.Prime 10009 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10009 10008 1 11 [2, 2, 2, 3, 3, 139]
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
    · apply IsUnit.of_mul_eq_one (5004 : ZMod 10009)
      decide
    · apply IsUnit.of_mul_eq_one (3684 : ZMod 10009)
      decide
    · apply IsUnit.of_mul_eq_one (578 : ZMod 10009)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10037 : Nat.Prime 10037 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10037 10036 1 2 [2, 2, 13, 193]
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
    · apply IsUnit.of_mul_eq_one (5018 : ZMod 10037)
      decide
    · apply IsUnit.of_mul_eq_one (7013 : ZMod 10037)
      decide
    · apply IsUnit.of_mul_eq_one (8757 : ZMod 10037)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10039 : Nat.Prime 10039 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10039 10038 1 3 [2, 3, 7, 239]
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
    · apply IsUnit.of_mul_eq_one (5019 : ZMod 10039)
      decide
    · apply IsUnit.of_mul_eq_one (2102 : ZMod 10039)
      decide
    · apply IsUnit.of_mul_eq_one (4557 : ZMod 10039)
      decide
    · apply IsUnit.of_mul_eq_one (468 : ZMod 10039)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10061 : Nat.Prime 10061 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10061 10060 1 3 [2, 2, 5, 503]
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
    · apply IsUnit.of_mul_eq_one (5030 : ZMod 10061)
      decide
    · apply IsUnit.of_mul_eq_one (8053 : ZMod 10061)
      decide
    · apply IsUnit.of_mul_eq_one (9565 : ZMod 10061)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10067 : Nat.Prime 10067 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10067 10066 1 2 [2, 7, 719]
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
    · apply IsUnit.of_mul_eq_one (5033 : ZMod 10067)
      decide
    · apply IsUnit.of_mul_eq_one (4295 : ZMod 10067)
      decide
    · apply IsUnit.of_mul_eq_one (3234 : ZMod 10067)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10069 : Nat.Prime 10069 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10069 10068 1 2 [2, 2, 3, 839]
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
    · apply IsUnit.of_mul_eq_one (5034 : ZMod 10069)
      decide
    · apply IsUnit.of_mul_eq_one (8500 : ZMod 10069)
      decide
    · apply IsUnit.of_mul_eq_one (986 : ZMod 10069)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10079 : Nat.Prime 10079 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10079 10078 1 11 [2, 5039]
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
    · apply IsUnit.of_mul_eq_one (5039 : ZMod 10079)
      decide
    · apply IsUnit.of_mul_eq_one (84 : ZMod 10079)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10091 : Nat.Prime 10091 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10091 10090 1 2 [2, 5, 1009]
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
    · apply IsUnit.of_mul_eq_one (5045 : ZMod 10091)
      decide
    · apply IsUnit.of_mul_eq_one (5246 : ZMod 10091)
      decide
    · apply IsUnit.of_mul_eq_one (1815 : ZMod 10091)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10093 : Nat.Prime 10093 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10093 10092 1 2 [2, 2, 3, 29, 29]
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
    · apply IsUnit.of_mul_eq_one (5046 : ZMod 10093)
      decide
    · apply IsUnit.of_mul_eq_one (5017 : ZMod 10093)
      decide
    · apply IsUnit.of_mul_eq_one (4299 : ZMod 10093)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10099 : Nat.Prime 10099 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10099 10098 1 2 [2, 3, 3, 3, 11, 17]
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
    · apply IsUnit.of_mul_eq_one (5049 : ZMod 10099)
      decide
    · apply IsUnit.of_mul_eq_one (8048 : ZMod 10099)
      decide
    · apply IsUnit.of_mul_eq_one (5324 : ZMod 10099)
      decide
    · apply IsUnit.of_mul_eq_one (1770 : ZMod 10099)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10103 : Nat.Prime 10103 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10103 10102 1 5 [2, 5051]
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
    · apply IsUnit.of_mul_eq_one (5051 : ZMod 10103)
      decide
    · apply IsUnit.of_mul_eq_one (421 : ZMod 10103)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10111 : Nat.Prime 10111 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10111 10110 1 12 [2, 3, 5, 337]
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
    · apply IsUnit.of_mul_eq_one (5055 : ZMod 10111)
      decide
    · apply IsUnit.of_mul_eq_one (5313 : ZMod 10111)
      decide
    · apply IsUnit.of_mul_eq_one (8110 : ZMod 10111)
      decide
    · apply IsUnit.of_mul_eq_one (2614 : ZMod 10111)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10133 : Nat.Prime 10133 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10133 10132 1 2 [2, 2, 17, 149]
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
    · apply IsUnit.of_mul_eq_one (5066 : ZMod 10133)
      decide
    · apply IsUnit.of_mul_eq_one (9859 : ZMod 10133)
      decide
    · apply IsUnit.of_mul_eq_one (6347 : ZMod 10133)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10139 : Nat.Prime 10139 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10139 10138 1 2 [2, 37, 137]
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
    · apply IsUnit.of_mul_eq_one (5069 : ZMod 10139)
      decide
    · apply IsUnit.of_mul_eq_one (9987 : ZMod 10139)
      decide
    · apply IsUnit.of_mul_eq_one (5073 : ZMod 10139)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10141 : Nat.Prime 10141 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10141 10140 1 2 [2, 2, 3, 5, 13, 13]
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
    · apply IsUnit.of_mul_eq_one (5070 : ZMod 10141)
      decide
    · apply IsUnit.of_mul_eq_one (9412 : ZMod 10141)
      decide
    · apply IsUnit.of_mul_eq_one (7257 : ZMod 10141)
      decide
    · apply IsUnit.of_mul_eq_one (5274 : ZMod 10141)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10151 : Nat.Prime 10151 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10151 10150 1 7 [2, 5, 5, 7, 29]
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
    · apply IsUnit.of_mul_eq_one (5075 : ZMod 10151)
      decide
    · apply IsUnit.of_mul_eq_one (757 : ZMod 10151)
      decide
    · apply IsUnit.of_mul_eq_one (3042 : ZMod 10151)
      decide
    · apply IsUnit.of_mul_eq_one (120 : ZMod 10151)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10159 : Nat.Prime 10159 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10159 10158 1 3 [2, 3, 1693]
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
    · apply IsUnit.of_mul_eq_one (5079 : ZMod 10159)
      decide
    · apply IsUnit.of_mul_eq_one (4917 : ZMod 10159)
      decide
    · apply IsUnit.of_mul_eq_one (4926 : ZMod 10159)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10163 : Nat.Prime 10163 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10163 10162 1 2 [2, 5081]
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
    · apply IsUnit.of_mul_eq_one (5081 : ZMod 10163)
      decide
    · apply IsUnit.of_mul_eq_one (3388 : ZMod 10163)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10169 : Nat.Prime 10169 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10169 10168 1 3 [2, 2, 2, 31, 41]
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
    · apply IsUnit.of_mul_eq_one (5084 : ZMod 10169)
      decide
    · apply IsUnit.of_mul_eq_one (10036 : ZMod 10169)
      decide
    · apply IsUnit.of_mul_eq_one (8135 : ZMod 10169)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10177 : Nat.Prime 10177 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10177 10176 1 7 [2, 2, 2, 2, 2, 2, 3, 53]
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
    · apply IsUnit.of_mul_eq_one (5088 : ZMod 10177)
      decide
    · apply IsUnit.of_mul_eq_one (5193 : ZMod 10177)
      decide
    · apply IsUnit.of_mul_eq_one (259 : ZMod 10177)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10181 : Nat.Prime 10181 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10181 10180 1 2 [2, 2, 5, 509]
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
    · apply IsUnit.of_mul_eq_one (5090 : ZMod 10181)
      decide
    · apply IsUnit.of_mul_eq_one (7224 : ZMod 10181)
      decide
    · apply IsUnit.of_mul_eq_one (3743 : ZMod 10181)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10193 : Nat.Prime 10193 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10193 10192 1 3 [2, 2, 2, 2, 7, 7, 13]
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
    · apply IsUnit.of_mul_eq_one (5096 : ZMod 10193)
      decide
    · apply IsUnit.of_mul_eq_one (2241 : ZMod 10193)
      decide
    · apply IsUnit.of_mul_eq_one (7140 : ZMod 10193)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10211 : Nat.Prime 10211 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10211 10210 1 6 [2, 5, 1021]
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
    · apply IsUnit.of_mul_eq_one (5105 : ZMod 10211)
      decide
    · apply IsUnit.of_mul_eq_one (3206 : ZMod 10211)
      decide
    · apply IsUnit.of_mul_eq_one (8076 : ZMod 10211)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10223 : Nat.Prime 10223 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10223 10222 1 5 [2, 19, 269]
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
    · apply IsUnit.of_mul_eq_one (5111 : ZMod 10223)
      decide
    · apply IsUnit.of_mul_eq_one (7259 : ZMod 10223)
      decide
    · apply IsUnit.of_mul_eq_one (5490 : ZMod 10223)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10243 : Nat.Prime 10243 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10243 10242 1 7 [2, 3, 3, 569]
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
    · apply IsUnit.of_mul_eq_one (5121 : ZMod 10243)
      decide
    · apply IsUnit.of_mul_eq_one (7016 : ZMod 10243)
      decide
    · apply IsUnit.of_mul_eq_one (1942 : ZMod 10243)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10247 : Nat.Prime 10247 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10247 10246 1 5 [2, 47, 109]
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
    · apply IsUnit.of_mul_eq_one (5123 : ZMod 10247)
      decide
    · apply IsUnit.of_mul_eq_one (4336 : ZMod 10247)
      decide
    · apply IsUnit.of_mul_eq_one (7615 : ZMod 10247)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10253 : Nat.Prime 10253 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10253 10252 1 2 [2, 2, 11, 233]
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
    · apply IsUnit.of_mul_eq_one (5126 : ZMod 10253)
      decide
    · apply IsUnit.of_mul_eq_one (2273 : ZMod 10253)
      decide
    · apply IsUnit.of_mul_eq_one (9846 : ZMod 10253)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10259 : Nat.Prime 10259 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10259 10258 1 2 [2, 23, 223]
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
    · apply IsUnit.of_mul_eq_one (5129 : ZMod 10259)
      decide
    · apply IsUnit.of_mul_eq_one (844 : ZMod 10259)
      decide
    · apply IsUnit.of_mul_eq_one (3520 : ZMod 10259)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10267 : Nat.Prime 10267 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10267 10266 1 2 [2, 3, 29, 59]
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
    · apply IsUnit.of_mul_eq_one (5133 : ZMod 10267)
      decide
    · apply IsUnit.of_mul_eq_one (58 : ZMod 10267)
      decide
    · apply IsUnit.of_mul_eq_one (2860 : ZMod 10267)
      decide
    · apply IsUnit.of_mul_eq_one (2107 : ZMod 10267)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10271 : Nat.Prime 10271 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10271 10270 1 7 [2, 5, 13, 79]
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
    · apply IsUnit.of_mul_eq_one (5135 : ZMod 10271)
      decide
    · apply IsUnit.of_mul_eq_one (9601 : ZMod 10271)
      decide
    · apply IsUnit.of_mul_eq_one (2070 : ZMod 10271)
      decide
    · apply IsUnit.of_mul_eq_one (9855 : ZMod 10271)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10273 : Nat.Prime 10273 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10273 10272 1 10 [2, 2, 2, 2, 2, 3, 107]
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
    · apply IsUnit.of_mul_eq_one (5136 : ZMod 10273)
      decide
    · apply IsUnit.of_mul_eq_one (6175 : ZMod 10273)
      decide
    · apply IsUnit.of_mul_eq_one (1401 : ZMod 10273)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10289 : Nat.Prime 10289 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10289 10288 1 3 [2, 2, 2, 2, 643]
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
    · apply IsUnit.of_mul_eq_one (5144 : ZMod 10289)
      decide
    · apply IsUnit.of_mul_eq_one (8718 : ZMod 10289)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10301 : Nat.Prime 10301 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10301 10300 1 2 [2, 2, 5, 5, 103]
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
    · apply IsUnit.of_mul_eq_one (5150 : ZMod 10301)
      decide
    · apply IsUnit.of_mul_eq_one (9185 : ZMod 10301)
      decide
    · apply IsUnit.of_mul_eq_one (8186 : ZMod 10301)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10303 : Nat.Prime 10303 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10303 10302 1 3 [2, 3, 17, 101]
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
    · apply IsUnit.of_mul_eq_one (5151 : ZMod 10303)
      decide
    · apply IsUnit.of_mul_eq_one (3400 : ZMod 10303)
      decide
    · apply IsUnit.of_mul_eq_one (1290 : ZMod 10303)
      decide
    · apply IsUnit.of_mul_eq_one (4197 : ZMod 10303)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10313 : Nat.Prime 10313 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10313 10312 1 3 [2, 2, 2, 1289]
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
    · apply IsUnit.of_mul_eq_one (5156 : ZMod 10313)
      decide
    · apply IsUnit.of_mul_eq_one (665 : ZMod 10313)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10321 : Nat.Prime 10321 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10321 10320 1 7 [2, 2, 2, 2, 3, 5, 43]
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
    · apply IsUnit.of_mul_eq_one (5160 : ZMod 10321)
      decide
    · apply IsUnit.of_mul_eq_one (7575 : ZMod 10321)
      decide
    · apply IsUnit.of_mul_eq_one (2095 : ZMod 10321)
      decide
    · apply IsUnit.of_mul_eq_one (8568 : ZMod 10321)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10331 : Nat.Prime 10331 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10331 10330 1 2 [2, 5, 1033]
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
    · apply IsUnit.of_mul_eq_one (5165 : ZMod 10331)
      decide
    · apply IsUnit.of_mul_eq_one (10168 : ZMod 10331)
      decide
    · apply IsUnit.of_mul_eq_one (7160 : ZMod 10331)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10333 : Nat.Prime 10333 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10333 10332 1 5 [2, 2, 3, 3, 7, 41]
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
    · apply IsUnit.of_mul_eq_one (5166 : ZMod 10333)
      decide
    · apply IsUnit.of_mul_eq_one (8077 : ZMod 10333)
      decide
    · apply IsUnit.of_mul_eq_one (6570 : ZMod 10333)
      decide
    · apply IsUnit.of_mul_eq_one (6858 : ZMod 10333)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10337 : Nat.Prime 10337 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10337 10336 1 3 [2, 2, 2, 2, 2, 17, 19]
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
    · apply IsUnit.of_mul_eq_one (5168 : ZMod 10337)
      decide
    · apply IsUnit.of_mul_eq_one (4136 : ZMod 10337)
      decide
    · apply IsUnit.of_mul_eq_one (8238 : ZMod 10337)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10343 : Nat.Prime 10343 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10343 10342 1 5 [2, 5171]
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
    · apply IsUnit.of_mul_eq_one (5171 : ZMod 10343)
      decide
    · apply IsUnit.of_mul_eq_one (431 : ZMod 10343)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10357 : Nat.Prime 10357 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10357 10356 1 2 [2, 2, 3, 863]
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
    · apply IsUnit.of_mul_eq_one (5178 : ZMod 10357)
      decide
    · apply IsUnit.of_mul_eq_one (8173 : ZMod 10357)
      decide
    · apply IsUnit.of_mul_eq_one (650 : ZMod 10357)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10369 : Nat.Prime 10369 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10369 10368 1 13 [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (5184 : ZMod 10369)
      decide
    · apply IsUnit.of_mul_eq_one (3178 : ZMod 10369)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10391 : Nat.Prime 10391 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10391 10390 1 19 [2, 5, 1039]
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
    · apply IsUnit.of_mul_eq_one (5195 : ZMod 10391)
      decide
    · apply IsUnit.of_mul_eq_one (4826 : ZMod 10391)
      decide
    · apply IsUnit.of_mul_eq_one (6067 : ZMod 10391)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10399 : Nat.Prime 10399 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10399 10398 1 6 [2, 3, 1733]
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
    · apply IsUnit.of_mul_eq_one (5199 : ZMod 10399)
      decide
    · apply IsUnit.of_mul_eq_one (3614 : ZMod 10399)
      decide
    · apply IsUnit.of_mul_eq_one (37 : ZMod 10399)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10427 : Nat.Prime 10427 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10427 10426 1 2 [2, 13, 401]
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
    · apply IsUnit.of_mul_eq_one (5213 : ZMod 10427)
      decide
    · apply IsUnit.of_mul_eq_one (6444 : ZMod 10427)
      decide
    · apply IsUnit.of_mul_eq_one (1177 : ZMod 10427)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10429 : Nat.Prime 10429 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10429 10428 1 7 [2, 2, 3, 11, 79]
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
    · apply IsUnit.of_mul_eq_one (5214 : ZMod 10429)
      decide
    · apply IsUnit.of_mul_eq_one (2671 : ZMod 10429)
      decide
    · apply IsUnit.of_mul_eq_one (1266 : ZMod 10429)
      decide
    · apply IsUnit.of_mul_eq_one (6072 : ZMod 10429)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10433 : Nat.Prime 10433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10433 10432 1 3 [2, 2, 2, 2, 2, 2, 163]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (5216 : ZMod 10433)
      decide
    · apply IsUnit.of_mul_eq_one (10059 : ZMod 10433)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10453 : Nat.Prime 10453 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10453 10452 1 5 [2, 2, 3, 13, 67]
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
    · apply IsUnit.of_mul_eq_one (5226 : ZMod 10453)
      decide
    · apply IsUnit.of_mul_eq_one (3574 : ZMod 10453)
      decide
    · apply IsUnit.of_mul_eq_one (2912 : ZMod 10453)
      decide
    · apply IsUnit.of_mul_eq_one (2197 : ZMod 10453)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10457 : Nat.Prime 10457 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10457 10456 1 3 [2, 2, 2, 1307]
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
    · apply IsUnit.of_mul_eq_one (5228 : ZMod 10457)
      decide
    · apply IsUnit.of_mul_eq_one (7025 : ZMod 10457)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10459 : Nat.Prime 10459 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10459 10458 1 2 [2, 3, 3, 7, 83]
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
    · apply IsUnit.of_mul_eq_one (5229 : ZMod 10459)
      decide
    · apply IsUnit.of_mul_eq_one (3929 : ZMod 10459)
      decide
    · apply IsUnit.of_mul_eq_one (6060 : ZMod 10459)
      decide
    · apply IsUnit.of_mul_eq_one (7039 : ZMod 10459)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10463 : Nat.Prime 10463 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10463 10462 1 5 [2, 5231]
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
    · apply IsUnit.of_mul_eq_one (5231 : ZMod 10463)
      decide
    · apply IsUnit.of_mul_eq_one (436 : ZMod 10463)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10477 : Nat.Prime 10477 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10477 10476 1 2 [2, 2, 3, 3, 3, 97]
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
    · apply IsUnit.of_mul_eq_one (5238 : ZMod 10477)
      decide
    · apply IsUnit.of_mul_eq_one (3253 : ZMod 10477)
      decide
    · apply IsUnit.of_mul_eq_one (278 : ZMod 10477)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10487 : Nat.Prime 10487 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10487 10486 1 5 [2, 7, 7, 107]
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
    · apply IsUnit.of_mul_eq_one (5243 : ZMod 10487)
      decide
    · apply IsUnit.of_mul_eq_one (7871 : ZMod 10487)
      decide
    · apply IsUnit.of_mul_eq_one (7201 : ZMod 10487)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10499 : Nat.Prime 10499 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10499 10498 1 2 [2, 29, 181]
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
    · apply IsUnit.of_mul_eq_one (5249 : ZMod 10499)
      decide
    · apply IsUnit.of_mul_eq_one (1425 : ZMod 10499)
      decide
    · apply IsUnit.of_mul_eq_one (8138 : ZMod 10499)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10501 : Nat.Prime 10501 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10501 10500 1 2 [2, 2, 3, 5, 5, 5, 7]
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
    · apply IsUnit.of_mul_eq_one (5250 : ZMod 10501)
      decide
    · apply IsUnit.of_mul_eq_one (1923 : ZMod 10501)
      decide
    · apply IsUnit.of_mul_eq_one (1149 : ZMod 10501)
      decide
    · apply IsUnit.of_mul_eq_one (1222 : ZMod 10501)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10513 : Nat.Prime 10513 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10513 10512 1 7 [2, 2, 2, 2, 3, 3, 73]
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
    · apply IsUnit.of_mul_eq_one (5256 : ZMod 10513)
      decide
    · apply IsUnit.of_mul_eq_one (1179 : ZMod 10513)
      decide
    · apply IsUnit.of_mul_eq_one (7656 : ZMod 10513)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10529 : Nat.Prime 10529 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10529 10528 1 3 [2, 2, 2, 2, 2, 7, 47]
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
    · apply IsUnit.of_mul_eq_one (5264 : ZMod 10529)
      decide
    · apply IsUnit.of_mul_eq_one (3668 : ZMod 10529)
      decide
    · apply IsUnit.of_mul_eq_one (5177 : ZMod 10529)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10531 : Nat.Prime 10531 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10531 10530 1 3 [2, 3, 3, 3, 3, 5, 13]
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
    · apply IsUnit.of_mul_eq_one (5265 : ZMod 10531)
      decide
    · apply IsUnit.of_mul_eq_one (1693 : ZMod 10531)
      decide
    · apply IsUnit.of_mul_eq_one (142 : ZMod 10531)
      decide
    · apply IsUnit.of_mul_eq_one (5324 : ZMod 10531)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10559 : Nat.Prime 10559 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10559 10558 1 23 [2, 5279]
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
    · apply IsUnit.of_mul_eq_one (5279 : ZMod 10559)
      decide
    · apply IsUnit.of_mul_eq_one (20 : ZMod 10559)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10567 : Nat.Prime 10567 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10567 10566 1 6 [2, 3, 3, 587]
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
    · apply IsUnit.of_mul_eq_one (5283 : ZMod 10567)
      decide
    · apply IsUnit.of_mul_eq_one (6649 : ZMod 10567)
      decide
    · apply IsUnit.of_mul_eq_one (3611 : ZMod 10567)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10589 : Nat.Prime 10589 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10589 10588 1 2 [2, 2, 2647]
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
    · apply IsUnit.of_mul_eq_one (5294 : ZMod 10589)
      decide
    · apply IsUnit.of_mul_eq_one (706 : ZMod 10589)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10597 : Nat.Prime 10597 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10597 10596 1 5 [2, 2, 3, 883]
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
    · apply IsUnit.of_mul_eq_one (5298 : ZMod 10597)
      decide
    · apply IsUnit.of_mul_eq_one (8994 : ZMod 10597)
      decide
    · apply IsUnit.of_mul_eq_one (4434 : ZMod 10597)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10601 : Nat.Prime 10601 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10601 10600 1 3 [2, 2, 2, 5, 5, 53]
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
    · apply IsUnit.of_mul_eq_one (5300 : ZMod 10601)
      decide
    · apply IsUnit.of_mul_eq_one (6830 : ZMod 10601)
      decide
    · apply IsUnit.of_mul_eq_one (8740 : ZMod 10601)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10607 : Nat.Prime 10607 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10607 10606 1 5 [2, 5303]
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
    · apply IsUnit.of_mul_eq_one (5303 : ZMod 10607)
      decide
    · apply IsUnit.of_mul_eq_one (442 : ZMod 10607)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10613 : Nat.Prime 10613 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10613 10612 1 2 [2, 2, 7, 379]
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
    · apply IsUnit.of_mul_eq_one (5306 : ZMod 10613)
      decide
    · apply IsUnit.of_mul_eq_one (3495 : ZMod 10613)
      decide
    · apply IsUnit.of_mul_eq_one (8518 : ZMod 10613)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10627 : Nat.Prime 10627 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10627 10626 1 5 [2, 3, 7, 11, 23]
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
    · apply IsUnit.of_mul_eq_one (5313 : ZMod 10627)
      decide
    · apply IsUnit.of_mul_eq_one (8513 : ZMod 10627)
      decide
    · apply IsUnit.of_mul_eq_one (6544 : ZMod 10627)
      decide
    · apply IsUnit.of_mul_eq_one (407 : ZMod 10627)
      decide
    · apply IsUnit.of_mul_eq_one (8102 : ZMod 10627)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10631 : Nat.Prime 10631 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10631 10630 1 11 [2, 5, 1063]
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
    · apply IsUnit.of_mul_eq_one (5315 : ZMod 10631)
      decide
    · apply IsUnit.of_mul_eq_one (479 : ZMod 10631)
      decide
    · apply IsUnit.of_mul_eq_one (4299 : ZMod 10631)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10639 : Nat.Prime 10639 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10639 10638 1 6 [2, 3, 3, 3, 197]
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
    · apply IsUnit.of_mul_eq_one (5319 : ZMod 10639)
      decide
    · apply IsUnit.of_mul_eq_one (4177 : ZMod 10639)
      decide
    · apply IsUnit.of_mul_eq_one (5916 : ZMod 10639)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10651 : Nat.Prime 10651 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10651 10650 1 7 [2, 3, 5, 5, 71]
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
    · apply IsUnit.of_mul_eq_one (5325 : ZMod 10651)
      decide
    · apply IsUnit.of_mul_eq_one (6772 : ZMod 10651)
      decide
    · apply IsUnit.of_mul_eq_one (395 : ZMod 10651)
      decide
    · apply IsUnit.of_mul_eq_one (10055 : ZMod 10651)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9769) (q := 9781) (by exact lowPrime_9781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9781) (q := 9787) (by exact lowPrime_9787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9787) (q := 9791) (by exact lowPrime_9791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9791) (q := 9803) (by exact lowPrime_9803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9803) (q := 9811) (by exact lowPrime_9811) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9811) (q := 9817) (by exact lowPrime_9817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9817) (q := 9829) (by exact lowPrime_9829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9829) (q := 9833) (by exact lowPrime_9833) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part06_chain :
    DusartPrimeRowsChain 9769 9832 dusartPrimeRows_9419_9900_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9897, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9833) (q := 9839) (by exact lowPrime_9839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9839) (q := 9851) (by exact lowPrime_9851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9851) (q := 9857) (by exact lowPrime_9857) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9857) (q := 9859) (by exact lowPrime_9859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9859) (q := 9871) (by exact lowPrime_9871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9871) (q := 9883) (by exact lowPrime_9883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9883) (q := 9887) (by exact lowPrime_9887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9887) (q := 9901) (by exact lowPrime_9901) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part07_chain :
    DusartPrimeRowsChain 9833 9900 dusartPrimeRows_9419_9900_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9897, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 9901) (q := 9907) (by exact lowPrime_9907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9907) (q := 9923) (by exact lowPrime_9923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9923) (q := 9929) (by exact lowPrime_9929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9929) (q := 9931) (by exact lowPrime_9931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9931) (q := 9941) (by exact lowPrime_9941) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9941) (q := 9949) (by exact lowPrime_9949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9949) (q := 9967) (by exact lowPrime_9967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9967) (q := 9973) (by exact lowPrime_9973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part01_chain :
    DusartPrimeRowsChain 9901 9972 dusartPrimeRows_9901_10426_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 9973) (q := 10007) (by exact lowPrime_10007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10007) (q := 10009) (by exact lowPrime_10009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10009) (q := 10037) (by exact lowPrime_10037) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10037) (q := 10039) (by exact lowPrime_10039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10039) (q := 10061) (by exact lowPrime_10061) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10061) (q := 10067) (by exact lowPrime_10067) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10067) (q := 10069) (by exact lowPrime_10069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10069) (q := 10079) (by exact lowPrime_10079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part02_chain :
    DusartPrimeRowsChain 9973 10078 dusartPrimeRows_9901_10426_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10079) (q := 10091) (by exact lowPrime_10091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10091) (q := 10093) (by exact lowPrime_10093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10093) (q := 10099) (by exact lowPrime_10099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10099) (q := 10103) (by exact lowPrime_10103) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10103) (q := 10111) (by exact lowPrime_10111) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10111) (q := 10133) (by exact lowPrime_10133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10133) (q := 10139) (by exact lowPrime_10139) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10139) (q := 10141) (by exact lowPrime_10141) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part03_chain :
    DusartPrimeRowsChain 10079 10140 dusartPrimeRows_9901_10426_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10141) (q := 10151) (by exact lowPrime_10151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10151) (q := 10159) (by exact lowPrime_10159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10159) (q := 10163) (by exact lowPrime_10163) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10163) (q := 10169) (by exact lowPrime_10169) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10169) (q := 10177) (by exact lowPrime_10177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10177) (q := 10181) (by exact lowPrime_10181) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10181) (q := 10193) (by exact lowPrime_10193) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10193) (q := 10211) (by exact lowPrime_10211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part04_chain :
    DusartPrimeRowsChain 10141 10210 dusartPrimeRows_9901_10426_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10211) (q := 10223) (by exact lowPrime_10223) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10223) (q := 10243) (by exact lowPrime_10243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10243) (q := 10247) (by exact lowPrime_10247) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10247) (q := 10253) (by exact lowPrime_10253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10253) (q := 10259) (by exact lowPrime_10259) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10259) (q := 10267) (by exact lowPrime_10267) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10267) (q := 10271) (by exact lowPrime_10271) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10271) (q := 10273) (by exact lowPrime_10273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part05_chain :
    DusartPrimeRowsChain 10211 10272 dusartPrimeRows_9901_10426_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10273) (q := 10289) (by exact lowPrime_10289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10289) (q := 10301) (by exact lowPrime_10301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10301) (q := 10303) (by exact lowPrime_10303) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10303) (q := 10313) (by exact lowPrime_10313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10313) (q := 10321) (by exact lowPrime_10321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10321) (q := 10331) (by exact lowPrime_10331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10331) (q := 10333) (by exact lowPrime_10333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10333) (q := 10337) (by exact lowPrime_10337) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part06_chain :
    DusartPrimeRowsChain 10273 10336 dusartPrimeRows_9901_10426_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10337) (q := 10343) (by exact lowPrime_10343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10343) (q := 10357) (by exact lowPrime_10357) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10357) (q := 10369) (by exact lowPrime_10369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10369) (q := 10391) (by exact lowPrime_10391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10391) (q := 10399) (by exact lowPrime_10399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10399) (q := 10427) (by exact lowPrime_10427) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part07_chain :
    DusartPrimeRowsChain 10337 10426 dusartPrimeRows_9901_10426_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.empty
              norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10427) (q := 10429) (by exact lowPrime_10429) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10429) (q := 10433) (by exact lowPrime_10433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10433) (q := 10453) (by exact lowPrime_10453) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10453) (q := 10457) (by exact lowPrime_10457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10457) (q := 10459) (by exact lowPrime_10459) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10459) (q := 10463) (by exact lowPrime_10463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10463) (q := 10477) (by exact lowPrime_10477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10477) (q := 10487) (by exact lowPrime_10487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part01_chain :
    DusartPrimeRowsChain 10427 10486 dusartPrimeRows_10427_10938_part01 := by
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
                  norm_num [dusartPrimeRow_of_explicit_10938, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10487) (q := 10499) (by exact lowPrime_10499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10499) (q := 10501) (by exact lowPrime_10501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10501) (q := 10513) (by exact lowPrime_10513) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10513) (q := 10529) (by exact lowPrime_10529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10529) (q := 10531) (by exact lowPrime_10531) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10531) (q := 10559) (by exact lowPrime_10559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10559) (q := 10567) (by exact lowPrime_10567) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10567) (q := 10589) (by exact lowPrime_10589) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part02_chain :
    DusartPrimeRowsChain 10487 10588 dusartPrimeRows_10427_10938_part02 := by
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
                  norm_num [dusartPrimeRow_of_explicit_10938, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10589) (q := 10597) (by exact lowPrime_10597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10597) (q := 10601) (by exact lowPrime_10601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10601) (q := 10607) (by exact lowPrime_10607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10607) (q := 10613) (by exact lowPrime_10613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10613) (q := 10627) (by exact lowPrime_10627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10627) (q := 10631) (by exact lowPrime_10631) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10631) (q := 10639) (by exact lowPrime_10639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10639) (q := 10651) (by exact lowPrime_10651) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part03_chain :
    DusartPrimeRowsChain 10589 10650 dusartPrimeRows_10427_10938_part03 := by
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
                  norm_num [dusartPrimeRow_of_explicit_10938, dusartPrimeRow_of_explicit_right]
