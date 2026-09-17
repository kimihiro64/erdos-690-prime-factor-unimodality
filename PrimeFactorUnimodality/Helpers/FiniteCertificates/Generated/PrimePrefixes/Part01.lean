import Mathlib.Tactic.IntervalCases
import PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive


set_option autoImplicit false

/-! Generated consecutive-prime chain and reusable exact prime prefixes. -/

namespace PrimeFactorUnimodality

/-- The empty reverse-ordered list of primes below two. -/
def primePrefix2 : List Nat := []

theorem primesBelow2_perm : (primesBelow 2).Perm primePrefix2 := by
  change ((Nat.primesBelow 2).sort (fun a b => a ≤ b)).Perm []
  rw [show Nat.primesBelow 2 = ∅ by
    ext q
    simp only [Nat.mem_primesBelow]
    simp only [Order.lt_two_iff, Finset.notMem_empty, iff_false, not_and]
    intro hq hprime
    exact (not_le_of_gt hprime.one_lt) hq]
  simp

theorem primePrefix2_gt_one : ∀ q ∈ primePrefix2, 1 < q := by
  simp [primePrefix2]

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive2_3 : ConsecutivePrimes 2 3 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  omega


/-- Generated reverse-ordered list of all primes below 3. -/
def primePrefix3 : List Nat :=
  2 :: primePrefix2

theorem primesBelow3_perm :
    (primesBelow 3).Perm primePrefix3 := by
  rw [primePrefix3]
  exact consecutive2_3.primesBelow_perm.trans
    (List.Perm.cons 2 primesBelow2_perm)

theorem primePrefix3_gt_one : ∀ q ∈ primePrefix3, 1 < q := by
  intro q hq
  rw [primePrefix3] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix2_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive3_5 : ConsecutivePrimes 3 5 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 5. -/
def primePrefix5 : List Nat :=
  3 :: primePrefix3

theorem primesBelow5_perm :
    (primesBelow 5).Perm primePrefix5 := by
  rw [primePrefix5]
  exact consecutive3_5.primesBelow_perm.trans
    (List.Perm.cons 3 primesBelow3_perm)

theorem primePrefix5_gt_one : ∀ q ∈ primePrefix5, 1 < q := by
  intro q hq
  rw [primePrefix5] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix3_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive5_7 : ConsecutivePrimes 5 7 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 7. -/
def primePrefix7 : List Nat :=
  5 :: primePrefix5

theorem primesBelow7_perm :
    (primesBelow 7).Perm primePrefix7 := by
  rw [primePrefix7]
  exact consecutive5_7.primesBelow_perm.trans
    (List.Perm.cons 5 primesBelow5_perm)

theorem primePrefix7_gt_one : ∀ q ∈ primePrefix7, 1 < q := by
  intro q hq
  rw [primePrefix7] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix5_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive7_11 : ConsecutivePrimes 7 11 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 11. -/
def primePrefix11 : List Nat :=
  7 :: primePrefix7

theorem primesBelow11_perm :
    (primesBelow 11).Perm primePrefix11 := by
  rw [primePrefix11]
  exact consecutive7_11.primesBelow_perm.trans
    (List.Perm.cons 7 primesBelow7_perm)

theorem primePrefix11_gt_one : ∀ q ∈ primePrefix11, 1 < q := by
  intro q hq
  rw [primePrefix11] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix7_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive11_13 : ConsecutivePrimes 11 13 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 13. -/
def primePrefix13 : List Nat :=
  11 :: primePrefix11

theorem primesBelow13_perm :
    (primesBelow 13).Perm primePrefix13 := by
  rw [primePrefix13]
  exact consecutive11_13.primesBelow_perm.trans
    (List.Perm.cons 11 primesBelow11_perm)

theorem primePrefix13_gt_one : ∀ q ∈ primePrefix13, 1 < q := by
  intro q hq
  rw [primePrefix13] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix11_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive13_17 : ConsecutivePrimes 13 17 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 17. -/
def primePrefix17 : List Nat :=
  13 :: primePrefix13

theorem primesBelow17_perm :
    (primesBelow 17).Perm primePrefix17 := by
  rw [primePrefix17]
  exact consecutive13_17.primesBelow_perm.trans
    (List.Perm.cons 13 primesBelow13_perm)

theorem primePrefix17_gt_one : ∀ q ∈ primePrefix17, 1 < q := by
  intro q hq
  rw [primePrefix17] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix13_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive17_19 : ConsecutivePrimes 17 19 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 19. -/
def primePrefix19 : List Nat :=
  17 :: primePrefix17

theorem primesBelow19_perm :
    (primesBelow 19).Perm primePrefix19 := by
  rw [primePrefix19]
  exact consecutive17_19.primesBelow_perm.trans
    (List.Perm.cons 17 primesBelow17_perm)

theorem primePrefix19_gt_one : ∀ q ∈ primePrefix19, 1 < q := by
  intro q hq
  rw [primePrefix19] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix17_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive19_23 : ConsecutivePrimes 19 23 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 23. -/
def primePrefix23 : List Nat :=
  19 :: primePrefix19

theorem primesBelow23_perm :
    (primesBelow 23).Perm primePrefix23 := by
  rw [primePrefix23]
  exact consecutive19_23.primesBelow_perm.trans
    (List.Perm.cons 19 primesBelow19_perm)

theorem primePrefix23_gt_one : ∀ q ∈ primePrefix23, 1 < q := by
  intro q hq
  rw [primePrefix23] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix19_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive23_29 : ConsecutivePrimes 23 29 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 29. -/
def primePrefix29 : List Nat :=
  23 :: primePrefix23

theorem primesBelow29_perm :
    (primesBelow 29).Perm primePrefix29 := by
  rw [primePrefix29]
  exact consecutive23_29.primesBelow_perm.trans
    (List.Perm.cons 23 primesBelow23_perm)

theorem primePrefix29_gt_one : ∀ q ∈ primePrefix29, 1 < q := by
  intro q hq
  rw [primePrefix29] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix23_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive29_31 : ConsecutivePrimes 29 31 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 31. -/
def primePrefix31 : List Nat :=
  29 :: primePrefix29

theorem primesBelow31_perm :
    (primesBelow 31).Perm primePrefix31 := by
  rw [primePrefix31]
  exact consecutive29_31.primesBelow_perm.trans
    (List.Perm.cons 29 primesBelow29_perm)

theorem primePrefix31_gt_one : ∀ q ∈ primePrefix31, 1 < q := by
  intro q hq
  rw [primePrefix31] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix29_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive31_37 : ConsecutivePrimes 31 37 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 37. -/
def primePrefix37 : List Nat :=
  31 :: primePrefix31

theorem primesBelow37_perm :
    (primesBelow 37).Perm primePrefix37 := by
  rw [primePrefix37]
  exact consecutive31_37.primesBelow_perm.trans
    (List.Perm.cons 31 primesBelow31_perm)

theorem primePrefix37_gt_one : ∀ q ∈ primePrefix37, 1 < q := by
  intro q hq
  rw [primePrefix37] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix31_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive37_41 : ConsecutivePrimes 37 41 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 41. -/
def primePrefix41 : List Nat :=
  37 :: primePrefix37

theorem primesBelow41_perm :
    (primesBelow 41).Perm primePrefix41 := by
  rw [primePrefix41]
  exact consecutive37_41.primesBelow_perm.trans
    (List.Perm.cons 37 primesBelow37_perm)

theorem primePrefix41_gt_one : ∀ q ∈ primePrefix41, 1 < q := by
  intro q hq
  rw [primePrefix41] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix37_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive41_43 : ConsecutivePrimes 41 43 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 43. -/
def primePrefix43 : List Nat :=
  41 :: primePrefix41

theorem primesBelow43_perm :
    (primesBelow 43).Perm primePrefix43 := by
  rw [primePrefix43]
  exact consecutive41_43.primesBelow_perm.trans
    (List.Perm.cons 41 primesBelow41_perm)

theorem primePrefix43_gt_one : ∀ q ∈ primePrefix43, 1 < q := by
  intro q hq
  rw [primePrefix43] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix41_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive43_47 : ConsecutivePrimes 43 47 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 47. -/
def primePrefix47 : List Nat :=
  43 :: primePrefix43

theorem primesBelow47_perm :
    (primesBelow 47).Perm primePrefix47 := by
  rw [primePrefix47]
  exact consecutive43_47.primesBelow_perm.trans
    (List.Perm.cons 43 primesBelow43_perm)

theorem primePrefix47_gt_one : ∀ q ∈ primePrefix47, 1 < q := by
  intro q hq
  rw [primePrefix47] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix43_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive47_53 : ConsecutivePrimes 47 53 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 53. -/
def primePrefix53 : List Nat :=
  47 :: primePrefix47

theorem primesBelow53_perm :
    (primesBelow 53).Perm primePrefix53 := by
  rw [primePrefix53]
  exact consecutive47_53.primesBelow_perm.trans
    (List.Perm.cons 47 primesBelow47_perm)

theorem primePrefix53_gt_one : ∀ q ∈ primePrefix53, 1 < q := by
  intro q hq
  rw [primePrefix53] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix47_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive53_59 : ConsecutivePrimes 53 59 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 59. -/
def primePrefix59 : List Nat :=
  53 :: primePrefix53

theorem primesBelow59_perm :
    (primesBelow 59).Perm primePrefix59 := by
  rw [primePrefix59]
  exact consecutive53_59.primesBelow_perm.trans
    (List.Perm.cons 53 primesBelow53_perm)

theorem primePrefix59_gt_one : ∀ q ∈ primePrefix59, 1 < q := by
  intro q hq
  rw [primePrefix59] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix53_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive59_61 : ConsecutivePrimes 59 61 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 61. -/
def primePrefix61 : List Nat :=
  59 :: primePrefix59

theorem primesBelow61_perm :
    (primesBelow 61).Perm primePrefix61 := by
  rw [primePrefix61]
  exact consecutive59_61.primesBelow_perm.trans
    (List.Perm.cons 59 primesBelow59_perm)

theorem primePrefix61_gt_one : ∀ q ∈ primePrefix61, 1 < q := by
  intro q hq
  rw [primePrefix61] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix59_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive61_67 : ConsecutivePrimes 61 67 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 67. -/
def primePrefix67 : List Nat :=
  61 :: primePrefix61

theorem primesBelow67_perm :
    (primesBelow 67).Perm primePrefix67 := by
  rw [primePrefix67]
  exact consecutive61_67.primesBelow_perm.trans
    (List.Perm.cons 61 primesBelow61_perm)

theorem primePrefix67_gt_one : ∀ q ∈ primePrefix67, 1 < q := by
  intro q hq
  rw [primePrefix67] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix61_gt_one q hq

end PrimeFactorUnimodality
