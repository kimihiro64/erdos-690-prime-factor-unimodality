import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 10 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10657 : Nat.Prime 10657 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10657 10656 1 7 [2, 2, 2, 2, 2, 3, 3, 37]
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
    · apply IsUnit.of_mul_eq_one (5328 : ZMod 10657)
      decide
    · apply IsUnit.of_mul_eq_one (8432 : ZMod 10657)
      decide
    · apply IsUnit.of_mul_eq_one (3738 : ZMod 10657)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10663 : Nat.Prime 10663 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10663 10662 1 3 [2, 3, 1777]
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
    · apply IsUnit.of_mul_eq_one (5331 : ZMod 10663)
      decide
    · apply IsUnit.of_mul_eq_one (7377 : ZMod 10663)
      decide
    · apply IsUnit.of_mul_eq_one (249 : ZMod 10663)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10667 : Nat.Prime 10667 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10667 10666 1 2 [2, 5333]
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
    · apply IsUnit.of_mul_eq_one (5333 : ZMod 10667)
      decide
    · apply IsUnit.of_mul_eq_one (3556 : ZMod 10667)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10687 : Nat.Prime 10687 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10687 10686 1 5 [2, 3, 13, 137]
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
    · apply IsUnit.of_mul_eq_one (5343 : ZMod 10687)
      decide
    · apply IsUnit.of_mul_eq_one (8342 : ZMod 10687)
      decide
    · apply IsUnit.of_mul_eq_one (6726 : ZMod 10687)
      decide
    · apply IsUnit.of_mul_eq_one (5794 : ZMod 10687)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10691 : Nat.Prime 10691 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10691 10690 1 2 [2, 5, 1069]
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
    · apply IsUnit.of_mul_eq_one (5345 : ZMod 10691)
      decide
    · apply IsUnit.of_mul_eq_one (5213 : ZMod 10691)
      decide
    · apply IsUnit.of_mul_eq_one (6563 : ZMod 10691)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10709 : Nat.Prime 10709 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10709 10708 1 2 [2, 2, 2677]
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
    · apply IsUnit.of_mul_eq_one (5354 : ZMod 10709)
      decide
    · apply IsUnit.of_mul_eq_one (714 : ZMod 10709)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10711 : Nat.Prime 10711 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10711 10710 1 3 [2, 3, 3, 5, 7, 17]
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
    · apply IsUnit.of_mul_eq_one (5355 : ZMod 10711)
      decide
    · apply IsUnit.of_mul_eq_one (5640 : ZMod 10711)
      decide
    · apply IsUnit.of_mul_eq_one (10234 : ZMod 10711)
      decide
    · apply IsUnit.of_mul_eq_one (8233 : ZMod 10711)
      decide
    · apply IsUnit.of_mul_eq_one (2620 : ZMod 10711)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10723 : Nat.Prime 10723 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10723 10722 1 2 [2, 3, 1787]
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
    · apply IsUnit.of_mul_eq_one (5361 : ZMod 10723)
      decide
    · apply IsUnit.of_mul_eq_one (10304 : ZMod 10723)
      decide
    · apply IsUnit.of_mul_eq_one (4936 : ZMod 10723)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10729 : Nat.Prime 10729 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10729 10728 1 7 [2, 2, 2, 3, 3, 149]
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
    · apply IsUnit.of_mul_eq_one (5364 : ZMod 10729)
      decide
    · apply IsUnit.of_mul_eq_one (7733 : ZMod 10729)
      decide
    · apply IsUnit.of_mul_eq_one (8551 : ZMod 10729)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10733 : Nat.Prime 10733 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10733 10732 1 2 [2, 2, 2683]
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
    · apply IsUnit.of_mul_eq_one (5366 : ZMod 10733)
      decide
    · apply IsUnit.of_mul_eq_one (9302 : ZMod 10733)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10739 : Nat.Prime 10739 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10739 10738 1 6 [2, 7, 13, 59]
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
    · apply IsUnit.of_mul_eq_one (5369 : ZMod 10739)
      decide
    · apply IsUnit.of_mul_eq_one (6302 : ZMod 10739)
      decide
    · apply IsUnit.of_mul_eq_one (5058 : ZMod 10739)
      decide
    · apply IsUnit.of_mul_eq_one (324 : ZMod 10739)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10753 : Nat.Prime 10753 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10753 10752 1 11 [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 7]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5376 : ZMod 10753)
      decide
    · apply IsUnit.of_mul_eq_one (1867 : ZMod 10753)
      decide
    · apply IsUnit.of_mul_eq_one (1268 : ZMod 10753)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10771 : Nat.Prime 10771 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10771 10770 1 3 [2, 3, 5, 359]
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
    · apply IsUnit.of_mul_eq_one (5385 : ZMod 10771)
      decide
    · apply IsUnit.of_mul_eq_one (5889 : ZMod 10771)
      decide
    · apply IsUnit.of_mul_eq_one (549 : ZMod 10771)
      decide
    · apply IsUnit.of_mul_eq_one (240 : ZMod 10771)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10781 : Nat.Prime 10781 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10781 10780 1 10 [2, 2, 5, 7, 7, 11]
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
    · apply IsUnit.of_mul_eq_one (5390 : ZMod 10781)
      decide
    · apply IsUnit.of_mul_eq_one (2787 : ZMod 10781)
      decide
    · apply IsUnit.of_mul_eq_one (834 : ZMod 10781)
      decide
    · apply IsUnit.of_mul_eq_one (2941 : ZMod 10781)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10789 : Nat.Prime 10789 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10789 10788 1 2 [2, 2, 3, 29, 31]
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
    · apply IsUnit.of_mul_eq_one (5394 : ZMod 10789)
      decide
    · apply IsUnit.of_mul_eq_one (4753 : ZMod 10789)
      decide
    · apply IsUnit.of_mul_eq_one (5037 : ZMod 10789)
      decide
    · apply IsUnit.of_mul_eq_one (9889 : ZMod 10789)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10799 : Nat.Prime 10799 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10799 10798 1 19 [2, 5399]
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
    · apply IsUnit.of_mul_eq_one (5399 : ZMod 10799)
      decide
    · apply IsUnit.of_mul_eq_one (30 : ZMod 10799)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10831 : Nat.Prime 10831 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10831 10830 1 7 [2, 3, 5, 19, 19]
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
    · apply IsUnit.of_mul_eq_one (5415 : ZMod 10831)
      decide
    · apply IsUnit.of_mul_eq_one (9708 : ZMod 10831)
      decide
    · apply IsUnit.of_mul_eq_one (2005 : ZMod 10831)
      decide
    · apply IsUnit.of_mul_eq_one (3346 : ZMod 10831)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10837 : Nat.Prime 10837 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10837 10836 1 2 [2, 2, 3, 3, 7, 43]
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
    · apply IsUnit.of_mul_eq_one (5418 : ZMod 10837)
      decide
    · apply IsUnit.of_mul_eq_one (1374 : ZMod 10837)
      decide
    · apply IsUnit.of_mul_eq_one (3536 : ZMod 10837)
      decide
    · apply IsUnit.of_mul_eq_one (5164 : ZMod 10837)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10847 : Nat.Prime 10847 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10847 10846 1 5 [2, 11, 17, 29]
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
    · apply IsUnit.of_mul_eq_one (5423 : ZMod 10847)
      decide
    · apply IsUnit.of_mul_eq_one (6321 : ZMod 10847)
      decide
    · apply IsUnit.of_mul_eq_one (10307 : ZMod 10847)
      decide
    · apply IsUnit.of_mul_eq_one (1699 : ZMod 10847)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10853 : Nat.Prime 10853 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10853 10852 1 2 [2, 2, 2713]
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
    · apply IsUnit.of_mul_eq_one (5426 : ZMod 10853)
      decide
    · apply IsUnit.of_mul_eq_one (9406 : ZMod 10853)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10859 : Nat.Prime 10859 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10859 10858 1 2 [2, 61, 89]
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
    · apply IsUnit.of_mul_eq_one (5429 : ZMod 10859)
      decide
    · apply IsUnit.of_mul_eq_one (1495 : ZMod 10859)
      decide
    · apply IsUnit.of_mul_eq_one (8212 : ZMod 10859)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10861 : Nat.Prime 10861 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10861 10860 1 2 [2, 2, 3, 5, 181]
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
    · apply IsUnit.of_mul_eq_one (5430 : ZMod 10861)
      decide
    · apply IsUnit.of_mul_eq_one (1399 : ZMod 10861)
      decide
    · apply IsUnit.of_mul_eq_one (7733 : ZMod 10861)
      decide
    · apply IsUnit.of_mul_eq_one (3891 : ZMod 10861)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10867 : Nat.Prime 10867 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10867 10866 1 2 [2, 3, 1811]
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
    · apply IsUnit.of_mul_eq_one (5433 : ZMod 10867)
      decide
    · apply IsUnit.of_mul_eq_one (2662 : ZMod 10867)
      decide
    · apply IsUnit.of_mul_eq_one (345 : ZMod 10867)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10883 : Nat.Prime 10883 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10883 10882 1 2 [2, 5441]
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
    · apply IsUnit.of_mul_eq_one (5441 : ZMod 10883)
      decide
    · apply IsUnit.of_mul_eq_one (3628 : ZMod 10883)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10889 : Nat.Prime 10889 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10889 10888 1 3 [2, 2, 2, 1361]
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
    · apply IsUnit.of_mul_eq_one (5444 : ZMod 10889)
      decide
    · apply IsUnit.of_mul_eq_one (8351 : ZMod 10889)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10891 : Nat.Prime 10891 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10891 10890 1 2 [2, 3, 3, 5, 11, 11]
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
    · apply IsUnit.of_mul_eq_one (5445 : ZMod 10891)
      decide
    · apply IsUnit.of_mul_eq_one (366 : ZMod 10891)
      decide
    · apply IsUnit.of_mul_eq_one (623 : ZMod 10891)
      decide
    · apply IsUnit.of_mul_eq_one (7029 : ZMod 10891)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10903 : Nat.Prime 10903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10903 10902 1 3 [2, 3, 23, 79]
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
    · apply IsUnit.of_mul_eq_one (5451 : ZMod 10903)
      decide
    · apply IsUnit.of_mul_eq_one (10743 : ZMod 10903)
      decide
    · apply IsUnit.of_mul_eq_one (680 : ZMod 10903)
      decide
    · apply IsUnit.of_mul_eq_one (3815 : ZMod 10903)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10909 : Nat.Prime 10909 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10909 10908 1 2 [2, 2, 3, 3, 3, 101]
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
    · apply IsUnit.of_mul_eq_one (5454 : ZMod 10909)
      decide
    · apply IsUnit.of_mul_eq_one (4183 : ZMod 10909)
      decide
    · apply IsUnit.of_mul_eq_one (10287 : ZMod 10909)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10937 : Nat.Prime 10937 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10937 10936 1 3 [2, 2, 2, 1367]
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
    · apply IsUnit.of_mul_eq_one (5468 : ZMod 10937)
      decide
    · apply IsUnit.of_mul_eq_one (8948 : ZMod 10937)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10939 : Nat.Prime 10939 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10939 10938 1 3 [2, 3, 1823]
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
    · apply IsUnit.of_mul_eq_one (5469 : ZMod 10939)
      decide
    · apply IsUnit.of_mul_eq_one (1465 : ZMod 10939)
      decide
    · apply IsUnit.of_mul_eq_one (9211 : ZMod 10939)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10949 : Nat.Prime 10949 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10949 10948 1 2 [2, 2, 7, 17, 23]
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
    · apply IsUnit.of_mul_eq_one (5474 : ZMod 10949)
      decide
    · apply IsUnit.of_mul_eq_one (7577 : ZMod 10949)
      decide
    · apply IsUnit.of_mul_eq_one (5820 : ZMod 10949)
      decide
    · apply IsUnit.of_mul_eq_one (10813 : ZMod 10949)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10957 : Nat.Prime 10957 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10957 10956 1 5 [2, 2, 3, 11, 83]
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
    · apply IsUnit.of_mul_eq_one (5478 : ZMod 10957)
      decide
    · apply IsUnit.of_mul_eq_one (9908 : ZMod 10957)
      decide
    · apply IsUnit.of_mul_eq_one (7368 : ZMod 10957)
      decide
    · apply IsUnit.of_mul_eq_one (2635 : ZMod 10957)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10973 : Nat.Prime 10973 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10973 10972 1 2 [2, 2, 13, 211]
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
    · apply IsUnit.of_mul_eq_one (5486 : ZMod 10973)
      decide
    · apply IsUnit.of_mul_eq_one (1173 : ZMod 10973)
      decide
    · apply IsUnit.of_mul_eq_one (1598 : ZMod 10973)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10979 : Nat.Prime 10979 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10979 10978 1 2 [2, 11, 499]
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
    · apply IsUnit.of_mul_eq_one (5489 : ZMod 10979)
      decide
    · apply IsUnit.of_mul_eq_one (5502 : ZMod 10979)
      decide
    · apply IsUnit.of_mul_eq_one (6959 : ZMod 10979)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10987 : Nat.Prime 10987 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10987 10986 1 2 [2, 3, 1831]
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
    · apply IsUnit.of_mul_eq_one (5493 : ZMod 10987)
      decide
    · apply IsUnit.of_mul_eq_one (8777 : ZMod 10987)
      decide
    · apply IsUnit.of_mul_eq_one (872 : ZMod 10987)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10993 : Nat.Prime 10993 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10993 10992 1 7 [2, 2, 2, 2, 3, 229]
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
    · apply IsUnit.of_mul_eq_one (5496 : ZMod 10993)
      decide
    · apply IsUnit.of_mul_eq_one (7843 : ZMod 10993)
      decide
    · apply IsUnit.of_mul_eq_one (5526 : ZMod 10993)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11003 : Nat.Prime 11003 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11003 11002 1 2 [2, 5501]
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
    · apply IsUnit.of_mul_eq_one (5501 : ZMod 11003)
      decide
    · apply IsUnit.of_mul_eq_one (3668 : ZMod 11003)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11027 : Nat.Prime 11027 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11027 11026 1 2 [2, 37, 149]
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
    · apply IsUnit.of_mul_eq_one (5513 : ZMod 11027)
      decide
    · apply IsUnit.of_mul_eq_one (10487 : ZMod 11027)
      decide
    · apply IsUnit.of_mul_eq_one (1519 : ZMod 11027)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11047 : Nat.Prime 11047 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11047 11046 1 3 [2, 3, 7, 263]
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
    · apply IsUnit.of_mul_eq_one (5523 : ZMod 11047)
      decide
    · apply IsUnit.of_mul_eq_one (7928 : ZMod 11047)
      decide
    · apply IsUnit.of_mul_eq_one (4502 : ZMod 11047)
      decide
    · apply IsUnit.of_mul_eq_one (9845 : ZMod 11047)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11057 : Nat.Prime 11057 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11057 11056 1 3 [2, 2, 2, 2, 691]
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
    · apply IsUnit.of_mul_eq_one (5528 : ZMod 11057)
      decide
    · apply IsUnit.of_mul_eq_one (1933 : ZMod 11057)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11059 : Nat.Prime 11059 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11059 11058 1 10 [2, 3, 19, 97]
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
    · apply IsUnit.of_mul_eq_one (5529 : ZMod 11059)
      decide
    · apply IsUnit.of_mul_eq_one (1435 : ZMod 11059)
      decide
    · apply IsUnit.of_mul_eq_one (4334 : ZMod 11059)
      decide
    · apply IsUnit.of_mul_eq_one (6582 : ZMod 11059)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11069 : Nat.Prime 11069 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11069 11068 1 2 [2, 2, 2767]
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
    · apply IsUnit.of_mul_eq_one (5534 : ZMod 11069)
      decide
    · apply IsUnit.of_mul_eq_one (738 : ZMod 11069)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11071 : Nat.Prime 11071 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11071 11070 1 3 [2, 3, 3, 3, 5, 41]
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
    · apply IsUnit.of_mul_eq_one (5535 : ZMod 11071)
      decide
    · apply IsUnit.of_mul_eq_one (10491 : ZMod 11071)
      decide
    · apply IsUnit.of_mul_eq_one (8769 : ZMod 11071)
      decide
    · apply IsUnit.of_mul_eq_one (3795 : ZMod 11071)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11083 : Nat.Prime 11083 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11083 11082 1 2 [2, 3, 1847]
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
    · apply IsUnit.of_mul_eq_one (5541 : ZMod 11083)
      decide
    · apply IsUnit.of_mul_eq_one (5153 : ZMod 11083)
      decide
    · apply IsUnit.of_mul_eq_one (6685 : ZMod 11083)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11087 : Nat.Prime 11087 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11087 11086 1 5 [2, 23, 241]
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
    · apply IsUnit.of_mul_eq_one (5543 : ZMod 11087)
      decide
    · apply IsUnit.of_mul_eq_one (1844 : ZMod 11087)
      decide
    · apply IsUnit.of_mul_eq_one (4718 : ZMod 11087)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11093 : Nat.Prime 11093 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11093 11092 1 2 [2, 2, 47, 59]
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
    · apply IsUnit.of_mul_eq_one (5546 : ZMod 11093)
      decide
    · apply IsUnit.of_mul_eq_one (7494 : ZMod 11093)
      decide
    · apply IsUnit.of_mul_eq_one (8300 : ZMod 11093)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11113 : Nat.Prime 11113 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11113 11112 1 13 [2, 2, 2, 3, 463]
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
    · apply IsUnit.of_mul_eq_one (5556 : ZMod 11113)
      decide
    · apply IsUnit.of_mul_eq_one (8694 : ZMod 11113)
      decide
    · apply IsUnit.of_mul_eq_one (6622 : ZMod 11113)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11117 : Nat.Prime 11117 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11117 11116 1 3 [2, 2, 7, 397]
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
    · apply IsUnit.of_mul_eq_one (5558 : ZMod 11117)
      decide
    · apply IsUnit.of_mul_eq_one (10199 : ZMod 11117)
      decide
    · apply IsUnit.of_mul_eq_one (3453 : ZMod 11117)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11119 : Nat.Prime 11119 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11119 11118 1 3 [2, 3, 17, 109]
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
    · apply IsUnit.of_mul_eq_one (5559 : ZMod 11119)
      decide
    · apply IsUnit.of_mul_eq_one (4491 : ZMod 11119)
      decide
    · apply IsUnit.of_mul_eq_one (353 : ZMod 11119)
      decide
    · apply IsUnit.of_mul_eq_one (9542 : ZMod 11119)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11131 : Nat.Prime 11131 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11131 11130 1 2 [2, 3, 5, 7, 53]
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
    · apply IsUnit.of_mul_eq_one (5565 : ZMod 11131)
      decide
    · apply IsUnit.of_mul_eq_one (7385 : ZMod 11131)
      decide
    · apply IsUnit.of_mul_eq_one (8646 : ZMod 11131)
      decide
    · apply IsUnit.of_mul_eq_one (5515 : ZMod 11131)
      decide
    · apply IsUnit.of_mul_eq_one (7635 : ZMod 11131)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11149 : Nat.Prime 11149 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11149 11148 1 10 [2, 2, 3, 929]
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
    · apply IsUnit.of_mul_eq_one (5574 : ZMod 11149)
      decide
    · apply IsUnit.of_mul_eq_one (9669 : ZMod 11149)
      decide
    · apply IsUnit.of_mul_eq_one (3656 : ZMod 11149)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11159 : Nat.Prime 11159 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11159 11158 1 7 [2, 7, 797]
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
    · apply IsUnit.of_mul_eq_one (5579 : ZMod 11159)
      decide
    · apply IsUnit.of_mul_eq_one (7029 : ZMod 11159)
      decide
    · apply IsUnit.of_mul_eq_one (8397 : ZMod 11159)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11161 : Nat.Prime 11161 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11161 11160 1 7 [2, 2, 2, 3, 3, 5, 31]
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
    · apply IsUnit.of_mul_eq_one (5580 : ZMod 11161)
      decide
    · apply IsUnit.of_mul_eq_one (4991 : ZMod 11161)
      decide
    · apply IsUnit.of_mul_eq_one (67 : ZMod 11161)
      decide
    · apply IsUnit.of_mul_eq_one (10508 : ZMod 11161)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11171 : Nat.Prime 11171 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11171 11170 1 2 [2, 5, 1117]
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
    · apply IsUnit.of_mul_eq_one (5585 : ZMod 11171)
      decide
    · apply IsUnit.of_mul_eq_one (10661 : ZMod 11171)
      decide
    · apply IsUnit.of_mul_eq_one (2861 : ZMod 11171)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11173 : Nat.Prime 11173 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11173 11172 1 5 [2, 2, 3, 7, 7, 19]
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
    · apply IsUnit.of_mul_eq_one (5586 : ZMod 11173)
      decide
    · apply IsUnit.of_mul_eq_one (8794 : ZMod 11173)
      decide
    · apply IsUnit.of_mul_eq_one (9650 : ZMod 11173)
      decide
    · apply IsUnit.of_mul_eq_one (10143 : ZMod 11173)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11177 : Nat.Prime 11177 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11177 11176 1 3 [2, 2, 2, 11, 127]
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
    · apply IsUnit.of_mul_eq_one (5588 : ZMod 11177)
      decide
    · apply IsUnit.of_mul_eq_one (8554 : ZMod 11177)
      decide
    · apply IsUnit.of_mul_eq_one (2494 : ZMod 11177)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11197 : Nat.Prime 11197 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11197 11196 1 2 [2, 2, 3, 3, 311]
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
    · apply IsUnit.of_mul_eq_one (5598 : ZMod 11197)
      decide
    · apply IsUnit.of_mul_eq_one (9729 : ZMod 11197)
      decide
    · apply IsUnit.of_mul_eq_one (858 : ZMod 11197)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11213 : Nat.Prime 11213 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11213 11212 1 2 [2, 2, 2803]
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
    · apply IsUnit.of_mul_eq_one (5606 : ZMod 11213)
      decide
    · apply IsUnit.of_mul_eq_one (9718 : ZMod 11213)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11239 : Nat.Prime 11239 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11239 11238 1 3 [2, 3, 1873]
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
    · apply IsUnit.of_mul_eq_one (5619 : ZMod 11239)
      decide
    · apply IsUnit.of_mul_eq_one (1855 : ZMod 11239)
      decide
    · apply IsUnit.of_mul_eq_one (1374 : ZMod 11239)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11243 : Nat.Prime 11243 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11243 11242 1 5 [2, 7, 11, 73]
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
    · apply IsUnit.of_mul_eq_one (5621 : ZMod 11243)
      decide
    · apply IsUnit.of_mul_eq_one (2575 : ZMod 11243)
      decide
    · apply IsUnit.of_mul_eq_one (1875 : ZMod 11243)
      decide
    · apply IsUnit.of_mul_eq_one (4369 : ZMod 11243)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11251 : Nat.Prime 11251 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11251 11250 1 13 [2, 3, 3, 5, 5, 5, 5]
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
    · apply IsUnit.of_mul_eq_one (5625 : ZMod 11251)
      decide
    · apply IsUnit.of_mul_eq_one (3391 : ZMod 11251)
      decide
    · apply IsUnit.of_mul_eq_one (9241 : ZMod 11251)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11257 : Nat.Prime 11257 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11257 11256 1 10 [2, 2, 2, 3, 7, 67]
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
    · apply IsUnit.of_mul_eq_one (5628 : ZMod 11257)
      decide
    · apply IsUnit.of_mul_eq_one (1440 : ZMod 11257)
      decide
    · apply IsUnit.of_mul_eq_one (7209 : ZMod 11257)
      decide
    · apply IsUnit.of_mul_eq_one (5797 : ZMod 11257)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11261 : Nat.Prime 11261 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11261 11260 1 2 [2, 2, 5, 563]
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
    · apply IsUnit.of_mul_eq_one (5630 : ZMod 11261)
      decide
    · apply IsUnit.of_mul_eq_one (7395 : ZMod 11261)
      decide
    · apply IsUnit.of_mul_eq_one (1306 : ZMod 11261)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11273 : Nat.Prime 11273 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11273 11272 1 3 [2, 2, 2, 1409]
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
    · apply IsUnit.of_mul_eq_one (5636 : ZMod 11273)
      decide
    · apply IsUnit.of_mul_eq_one (177 : ZMod 11273)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11279 : Nat.Prime 11279 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11279 11278 1 7 [2, 5639]
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
    · apply IsUnit.of_mul_eq_one (5639 : ZMod 11279)
      decide
    · apply IsUnit.of_mul_eq_one (235 : ZMod 11279)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11287 : Nat.Prime 11287 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11287 11286 1 3 [2, 3, 3, 3, 11, 19]
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
    · apply IsUnit.of_mul_eq_one (5643 : ZMod 11287)
      decide
    · apply IsUnit.of_mul_eq_one (6125 : ZMod 11287)
      decide
    · apply IsUnit.of_mul_eq_one (6438 : ZMod 11287)
      decide
    · apply IsUnit.of_mul_eq_one (11248 : ZMod 11287)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11299 : Nat.Prime 11299 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11299 11298 1 3 [2, 3, 7, 269]
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
    · apply IsUnit.of_mul_eq_one (5649 : ZMod 11299)
      decide
    · apply IsUnit.of_mul_eq_one (3266 : ZMod 11299)
      decide
    · apply IsUnit.of_mul_eq_one (2700 : ZMod 11299)
      decide
    · apply IsUnit.of_mul_eq_one (2206 : ZMod 11299)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11311 : Nat.Prime 11311 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11311 11310 1 3 [2, 3, 5, 13, 29]
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
    · apply IsUnit.of_mul_eq_one (5655 : ZMod 11311)
      decide
    · apply IsUnit.of_mul_eq_one (373 : ZMod 11311)
      decide
    · apply IsUnit.of_mul_eq_one (2845 : ZMod 11311)
      decide
    · apply IsUnit.of_mul_eq_one (4907 : ZMod 11311)
      decide
    · apply IsUnit.of_mul_eq_one (3474 : ZMod 11311)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11317 : Nat.Prime 11317 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11317 11316 1 2 [2, 2, 3, 23, 41]
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
    · apply IsUnit.of_mul_eq_one (5658 : ZMod 11317)
      decide
    · apply IsUnit.of_mul_eq_one (162 : ZMod 11317)
      decide
    · apply IsUnit.of_mul_eq_one (11176 : ZMod 11317)
      decide
    · apply IsUnit.of_mul_eq_one (8783 : ZMod 11317)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11321 : Nat.Prime 11321 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11321 11320 1 3 [2, 2, 2, 5, 283]
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
    · apply IsUnit.of_mul_eq_one (5660 : ZMod 11321)
      decide
    · apply IsUnit.of_mul_eq_one (3925 : ZMod 11321)
      decide
    · apply IsUnit.of_mul_eq_one (6183 : ZMod 11321)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11329 : Nat.Prime 11329 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11329 11328 1 7 [2, 2, 2, 2, 2, 2, 3, 59]
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
    · apply IsUnit.of_mul_eq_one (5664 : ZMod 11329)
      decide
    · apply IsUnit.of_mul_eq_one (7143 : ZMod 11329)
      decide
    · apply IsUnit.of_mul_eq_one (7509 : ZMod 11329)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11351 : Nat.Prime 11351 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11351 11350 1 7 [2, 5, 5, 227]
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
    · apply IsUnit.of_mul_eq_one (5675 : ZMod 11351)
      decide
    · apply IsUnit.of_mul_eq_one (1332 : ZMod 11351)
      decide
    · apply IsUnit.of_mul_eq_one (1949 : ZMod 11351)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11353 : Nat.Prime 11353 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11353 11352 1 7 [2, 2, 2, 3, 11, 43]
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
    · apply IsUnit.of_mul_eq_one (5676 : ZMod 11353)
      decide
    · apply IsUnit.of_mul_eq_one (6799 : ZMod 11353)
      decide
    · apply IsUnit.of_mul_eq_one (6163 : ZMod 11353)
      decide
    · apply IsUnit.of_mul_eq_one (5853 : ZMod 11353)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11369 : Nat.Prime 11369 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11369 11368 1 3 [2, 2, 2, 7, 7, 29]
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
    · apply IsUnit.of_mul_eq_one (5684 : ZMod 11369)
      decide
    · apply IsUnit.of_mul_eq_one (4068 : ZMod 11369)
      decide
    · apply IsUnit.of_mul_eq_one (742 : ZMod 11369)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11383 : Nat.Prime 11383 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11383 11382 1 5 [2, 3, 7, 271]
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
    · apply IsUnit.of_mul_eq_one (5691 : ZMod 11383)
      decide
    · apply IsUnit.of_mul_eq_one (11114 : ZMod 11383)
      decide
    · apply IsUnit.of_mul_eq_one (9056 : ZMod 11383)
      decide
    · apply IsUnit.of_mul_eq_one (1210 : ZMod 11383)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11393 : Nat.Prime 11393 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11393 11392 1 3 [2, 2, 2, 2, 2, 2, 2, 89]
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
    · apply IsUnit.of_mul_eq_one (5696 : ZMod 11393)
      decide
    · apply IsUnit.of_mul_eq_one (9239 : ZMod 11393)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11399 : Nat.Prime 11399 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11399 11398 1 11 [2, 41, 139]
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
    · apply IsUnit.of_mul_eq_one (5699 : ZMod 11399)
      decide
    · apply IsUnit.of_mul_eq_one (5165 : ZMod 11399)
      decide
    · apply IsUnit.of_mul_eq_one (588 : ZMod 11399)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11411 : Nat.Prime 11411 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11411 11410 1 7 [2, 5, 7, 163]
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
    · apply IsUnit.of_mul_eq_one (5705 : ZMod 11411)
      decide
    · apply IsUnit.of_mul_eq_one (3032 : ZMod 11411)
      decide
    · apply IsUnit.of_mul_eq_one (5665 : ZMod 11411)
      decide
    · apply IsUnit.of_mul_eq_one (1006 : ZMod 11411)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11423 : Nat.Prime 11423 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11423 11422 1 5 [2, 5711]
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
    · apply IsUnit.of_mul_eq_one (5711 : ZMod 11423)
      decide
    · apply IsUnit.of_mul_eq_one (476 : ZMod 11423)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11437 : Nat.Prime 11437 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11437 11436 1 2 [2, 2, 3, 953]
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
    · apply IsUnit.of_mul_eq_one (5718 : ZMod 11437)
      decide
    · apply IsUnit.of_mul_eq_one (8430 : ZMod 11437)
      decide
    · apply IsUnit.of_mul_eq_one (2603 : ZMod 11437)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11443 : Nat.Prime 11443 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11443 11442 1 2 [2, 3, 1907]
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
    · apply IsUnit.of_mul_eq_one (5721 : ZMod 11443)
      decide
    · apply IsUnit.of_mul_eq_one (4791 : ZMod 11443)
      decide
    · apply IsUnit.of_mul_eq_one (1998 : ZMod 11443)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11447 : Nat.Prime 11447 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11447 11446 1 5 [2, 59, 97]
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
    · apply IsUnit.of_mul_eq_one (5723 : ZMod 11447)
      decide
    · apply IsUnit.of_mul_eq_one (6951 : ZMod 11447)
      decide
    · apply IsUnit.of_mul_eq_one (3249 : ZMod 11447)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11467 : Nat.Prime 11467 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11467 11466 1 5 [2, 3, 3, 7, 7, 13]
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
    · apply IsUnit.of_mul_eq_one (5733 : ZMod 11467)
      decide
    · apply IsUnit.of_mul_eq_one (8778 : ZMod 11467)
      decide
    · apply IsUnit.of_mul_eq_one (530 : ZMod 11467)
      decide
    · apply IsUnit.of_mul_eq_one (9817 : ZMod 11467)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11471 : Nat.Prime 11471 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11471 11470 1 11 [2, 5, 31, 37]
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
    · apply IsUnit.of_mul_eq_one (5735 : ZMod 11471)
      decide
    · apply IsUnit.of_mul_eq_one (5662 : ZMod 11471)
      decide
    · apply IsUnit.of_mul_eq_one (7362 : ZMod 11471)
      decide
    · apply IsUnit.of_mul_eq_one (4372 : ZMod 11471)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11483 : Nat.Prime 11483 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11483 11482 1 2 [2, 5741]
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
    · apply IsUnit.of_mul_eq_one (5741 : ZMod 11483)
      decide
    · apply IsUnit.of_mul_eq_one (3828 : ZMod 11483)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11489 : Nat.Prime 11489 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11489 11488 1 3 [2, 2, 2, 2, 2, 359]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (5744 : ZMod 11489)
      decide
    · apply IsUnit.of_mul_eq_one (1620 : ZMod 11489)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11491 : Nat.Prime 11491 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11491 11490 1 3 [2, 3, 5, 383]
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
    · apply IsUnit.of_mul_eq_one (5745 : ZMod 11491)
      decide
    · apply IsUnit.of_mul_eq_one (3701 : ZMod 11491)
      decide
    · apply IsUnit.of_mul_eq_one (3078 : ZMod 11491)
      decide
    · apply IsUnit.of_mul_eq_one (6464 : ZMod 11491)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11497 : Nat.Prime 11497 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11497 11496 1 7 [2, 2, 2, 3, 479]
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
    · apply IsUnit.of_mul_eq_one (5748 : ZMod 11497)
      decide
    · apply IsUnit.of_mul_eq_one (483 : ZMod 11497)
      decide
    · apply IsUnit.of_mul_eq_one (7895 : ZMod 11497)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11503 : Nat.Prime 11503 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11503 11502 1 3 [2, 3, 3, 3, 3, 71]
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
    · apply IsUnit.of_mul_eq_one (5751 : ZMod 11503)
      decide
    · apply IsUnit.of_mul_eq_one (3678 : ZMod 11503)
      decide
    · apply IsUnit.of_mul_eq_one (6309 : ZMod 11503)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10651) (q := 10657) (by exact lowPrime_10657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10657) (q := 10663) (by exact lowPrime_10663) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10663) (q := 10667) (by exact lowPrime_10667) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10667) (q := 10687) (by exact lowPrime_10687) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10687) (q := 10691) (by exact lowPrime_10691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10691) (q := 10709) (by exact lowPrime_10709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10709) (q := 10711) (by exact lowPrime_10711) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10711) (q := 10723) (by exact lowPrime_10723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part04_chain :
    DusartPrimeRowsChain 10651 10722 dusartPrimeRows_10427_10938_part04 := by
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
def dusartPrimeRows_10427_10938_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10723) (q := 10729) (by exact lowPrime_10729) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10729) (q := 10733) (by exact lowPrime_10733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10733) (q := 10739) (by exact lowPrime_10739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10739) (q := 10753) (by exact lowPrime_10753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10753) (q := 10771) (by exact lowPrime_10771) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10771) (q := 10781) (by exact lowPrime_10781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10781) (q := 10789) (by exact lowPrime_10789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10789) (q := 10799) (by exact lowPrime_10799) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part05_chain :
    DusartPrimeRowsChain 10723 10798 dusartPrimeRows_10427_10938_part05 := by
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
def dusartPrimeRows_10427_10938_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10799) (q := 10831) (by exact lowPrime_10831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10831) (q := 10837) (by exact lowPrime_10837) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10837) (q := 10847) (by exact lowPrime_10847) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10847) (q := 10853) (by exact lowPrime_10853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10853) (q := 10859) (by exact lowPrime_10859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10859) (q := 10861) (by exact lowPrime_10861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10861) (q := 10867) (by exact lowPrime_10867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10867) (q := 10883) (by exact lowPrime_10883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part06_chain :
    DusartPrimeRowsChain 10799 10882 dusartPrimeRows_10427_10938_part06 := by
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
def dusartPrimeRows_10427_10938_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10883) (q := 10889) (by exact lowPrime_10889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10889) (q := 10891) (by exact lowPrime_10891) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10891) (q := 10903) (by exact lowPrime_10903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10903) (q := 10909) (by exact lowPrime_10909) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10909) (q := 10937) (by exact lowPrime_10937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10937) (q := 10939) (by exact lowPrime_10939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part07_chain :
    DusartPrimeRowsChain 10883 10938 dusartPrimeRows_10427_10938_part07 := by
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
            · apply DusartPrimeRowsChain.empty
              norm_num [dusartPrimeRow_of_explicit_10938, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 10939) (q := 10949) (by exact lowPrime_10949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10949) (q := 10957) (by exact lowPrime_10957) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10957) (q := 10973) (by exact lowPrime_10973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10973) (q := 10979) (by exact lowPrime_10979) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10979) (q := 10987) (by exact lowPrime_10987) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10987) (q := 10993) (by exact lowPrime_10993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10993) (q := 11003) (by exact lowPrime_11003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11003) (q := 11027) (by exact lowPrime_11027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part01_chain :
    DusartPrimeRowsChain 10939 11026 dusartPrimeRows_10939_11502_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11027) (q := 11047) (by exact lowPrime_11047) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11047) (q := 11057) (by exact lowPrime_11057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11057) (q := 11059) (by exact lowPrime_11059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11059) (q := 11069) (by exact lowPrime_11069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11069) (q := 11071) (by exact lowPrime_11071) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11071) (q := 11083) (by exact lowPrime_11083) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11083) (q := 11087) (by exact lowPrime_11087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11087) (q := 11093) (by exact lowPrime_11093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part02_chain :
    DusartPrimeRowsChain 11027 11092 dusartPrimeRows_10939_11502_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11093) (q := 11113) (by exact lowPrime_11113) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11113) (q := 11117) (by exact lowPrime_11117) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11117) (q := 11119) (by exact lowPrime_11119) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11119) (q := 11131) (by exact lowPrime_11131) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11131) (q := 11149) (by exact lowPrime_11149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11149) (q := 11159) (by exact lowPrime_11159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11159) (q := 11161) (by exact lowPrime_11161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11161) (q := 11171) (by exact lowPrime_11171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part03_chain :
    DusartPrimeRowsChain 11093 11170 dusartPrimeRows_10939_11502_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11171) (q := 11173) (by exact lowPrime_11173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11173) (q := 11177) (by exact lowPrime_11177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11177) (q := 11197) (by exact lowPrime_11197) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11197) (q := 11213) (by exact lowPrime_11213) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11213) (q := 11239) (by exact lowPrime_11239) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11239) (q := 11243) (by exact lowPrime_11243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11243) (q := 11251) (by exact lowPrime_11251) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11251) (q := 11257) (by exact lowPrime_11257) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part04_chain :
    DusartPrimeRowsChain 11171 11256 dusartPrimeRows_10939_11502_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11257) (q := 11261) (by exact lowPrime_11261) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11261) (q := 11273) (by exact lowPrime_11273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11273) (q := 11279) (by exact lowPrime_11279) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11279) (q := 11287) (by exact lowPrime_11287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11287) (q := 11299) (by exact lowPrime_11299) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11299) (q := 11311) (by exact lowPrime_11311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11311) (q := 11317) (by exact lowPrime_11317) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11317) (q := 11321) (by exact lowPrime_11321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part05_chain :
    DusartPrimeRowsChain 11257 11320 dusartPrimeRows_10939_11502_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11321) (q := 11329) (by exact lowPrime_11329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11329) (q := 11351) (by exact lowPrime_11351) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11351) (q := 11353) (by exact lowPrime_11353) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11353) (q := 11369) (by exact lowPrime_11369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11369) (q := 11383) (by exact lowPrime_11383) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11383) (q := 11393) (by exact lowPrime_11393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11393) (q := 11399) (by exact lowPrime_11399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11399) (q := 11411) (by exact lowPrime_11411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part06_chain :
    DusartPrimeRowsChain 11321 11410 dusartPrimeRows_10939_11502_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11411) (q := 11423) (by exact lowPrime_11423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11423) (q := 11437) (by exact lowPrime_11437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11437) (q := 11443) (by exact lowPrime_11443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11443) (q := 11447) (by exact lowPrime_11447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11447) (q := 11467) (by exact lowPrime_11467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11467) (q := 11471) (by exact lowPrime_11471) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11471) (q := 11483) (by exact lowPrime_11483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11483) (q := 11489) (by exact lowPrime_11489) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part07_chain :
    DusartPrimeRowsChain 11411 11488 dusartPrimeRows_10939_11502_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11489) (q := 11491) (by exact lowPrime_11491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11491) (q := 11497) (by exact lowPrime_11497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11497) (q := 11503) (by exact lowPrime_11503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part08_chain :
    DusartPrimeRowsChain 11489 11502 dusartPrimeRows_10939_11502_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.empty
        norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]
