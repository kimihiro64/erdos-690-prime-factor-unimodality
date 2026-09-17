import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes.Part07


set_option autoImplicit false

/-! Generated consecutive-prime chain and reusable exact prime prefixes. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive709_719 : ConsecutivePrimes 709 719 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 719. -/
def primePrefix719 : List Nat :=
  709 :: primePrefix709

theorem primesBelow719_perm :
    (primesBelow 719).Perm primePrefix719 := by
  rw [primePrefix719]
  exact consecutive709_719.primesBelow_perm.trans
    (List.Perm.cons 709 primesBelow709_perm)

theorem primePrefix719_gt_one : ∀ q ∈ primePrefix719, 1 < q := by
  intro q hq
  rw [primePrefix719] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix709_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive719_727 : ConsecutivePrimes 719 727 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 727. -/
def primePrefix727 : List Nat :=
  719 :: primePrefix719

theorem primesBelow727_perm :
    (primesBelow 727).Perm primePrefix727 := by
  rw [primePrefix727]
  exact consecutive719_727.primesBelow_perm.trans
    (List.Perm.cons 719 primesBelow719_perm)

theorem primePrefix727_gt_one : ∀ q ∈ primePrefix727, 1 < q := by
  intro q hq
  rw [primePrefix727] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix719_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive727_733 : ConsecutivePrimes 727 733 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 733. -/
def primePrefix733 : List Nat :=
  727 :: primePrefix727

theorem primesBelow733_perm :
    (primesBelow 733).Perm primePrefix733 := by
  rw [primePrefix733]
  exact consecutive727_733.primesBelow_perm.trans
    (List.Perm.cons 727 primesBelow727_perm)

theorem primePrefix733_gt_one : ∀ q ∈ primePrefix733, 1 < q := by
  intro q hq
  rw [primePrefix733] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix727_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive733_739 : ConsecutivePrimes 733 739 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 739. -/
def primePrefix739 : List Nat :=
  733 :: primePrefix733

theorem primesBelow739_perm :
    (primesBelow 739).Perm primePrefix739 := by
  rw [primePrefix739]
  exact consecutive733_739.primesBelow_perm.trans
    (List.Perm.cons 733 primesBelow733_perm)

theorem primePrefix739_gt_one : ∀ q ∈ primePrefix739, 1 < q := by
  intro q hq
  rw [primePrefix739] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix733_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive739_743 : ConsecutivePrimes 739 743 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 743. -/
def primePrefix743 : List Nat :=
  739 :: primePrefix739

theorem primesBelow743_perm :
    (primesBelow 743).Perm primePrefix743 := by
  rw [primePrefix743]
  exact consecutive739_743.primesBelow_perm.trans
    (List.Perm.cons 739 primesBelow739_perm)

theorem primePrefix743_gt_one : ∀ q ∈ primePrefix743, 1 < q := by
  intro q hq
  rw [primePrefix743] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix739_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive743_751 : ConsecutivePrimes 743 751 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 751. -/
def primePrefix751 : List Nat :=
  743 :: primePrefix743

theorem primesBelow751_perm :
    (primesBelow 751).Perm primePrefix751 := by
  rw [primePrefix751]
  exact consecutive743_751.primesBelow_perm.trans
    (List.Perm.cons 743 primesBelow743_perm)

theorem primePrefix751_gt_one : ∀ q ∈ primePrefix751, 1 < q := by
  intro q hq
  rw [primePrefix751] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix743_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive751_757 : ConsecutivePrimes 751 757 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 757. -/
def primePrefix757 : List Nat :=
  751 :: primePrefix751

theorem primesBelow757_perm :
    (primesBelow 757).Perm primePrefix757 := by
  rw [primePrefix757]
  exact consecutive751_757.primesBelow_perm.trans
    (List.Perm.cons 751 primesBelow751_perm)

theorem primePrefix757_gt_one : ∀ q ∈ primePrefix757, 1 < q := by
  intro q hq
  rw [primePrefix757] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix751_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive757_761 : ConsecutivePrimes 757 761 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 761. -/
def primePrefix761 : List Nat :=
  757 :: primePrefix757

theorem primesBelow761_perm :
    (primesBelow 761).Perm primePrefix761 := by
  rw [primePrefix761]
  exact consecutive757_761.primesBelow_perm.trans
    (List.Perm.cons 757 primesBelow757_perm)

theorem primePrefix761_gt_one : ∀ q ∈ primePrefix761, 1 < q := by
  intro q hq
  rw [primePrefix761] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix757_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive761_769 : ConsecutivePrimes 761 769 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 769. -/
def primePrefix769 : List Nat :=
  761 :: primePrefix761

theorem primesBelow769_perm :
    (primesBelow 769).Perm primePrefix769 := by
  rw [primePrefix769]
  exact consecutive761_769.primesBelow_perm.trans
    (List.Perm.cons 761 primesBelow761_perm)

theorem primePrefix769_gt_one : ∀ q ∈ primePrefix769, 1 < q := by
  intro q hq
  rw [primePrefix769] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix761_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive769_773 : ConsecutivePrimes 769 773 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 773. -/
def primePrefix773 : List Nat :=
  769 :: primePrefix769

theorem primesBelow773_perm :
    (primesBelow 773).Perm primePrefix773 := by
  rw [primePrefix773]
  exact consecutive769_773.primesBelow_perm.trans
    (List.Perm.cons 769 primesBelow769_perm)

theorem primePrefix773_gt_one : ∀ q ∈ primePrefix773, 1 < q := by
  intro q hq
  rw [primePrefix773] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix769_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive773_787 : ConsecutivePrimes 773 787 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 787. -/
def primePrefix787 : List Nat :=
  773 :: primePrefix773

theorem primesBelow787_perm :
    (primesBelow 787).Perm primePrefix787 := by
  rw [primePrefix787]
  exact consecutive773_787.primesBelow_perm.trans
    (List.Perm.cons 773 primesBelow773_perm)

theorem primePrefix787_gt_one : ∀ q ∈ primePrefix787, 1 < q := by
  intro q hq
  rw [primePrefix787] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix773_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive787_797 : ConsecutivePrimes 787 797 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 797. -/
def primePrefix797 : List Nat :=
  787 :: primePrefix787

theorem primesBelow797_perm :
    (primesBelow 797).Perm primePrefix797 := by
  rw [primePrefix797]
  exact consecutive787_797.primesBelow_perm.trans
    (List.Perm.cons 787 primesBelow787_perm)

theorem primePrefix797_gt_one : ∀ q ∈ primePrefix797, 1 < q := by
  intro q hq
  rw [primePrefix797] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix787_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive797_809 : ConsecutivePrimes 797 809 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 809. -/
def primePrefix809 : List Nat :=
  797 :: primePrefix797

theorem primesBelow809_perm :
    (primesBelow 809).Perm primePrefix809 := by
  rw [primePrefix809]
  exact consecutive797_809.primesBelow_perm.trans
    (List.Perm.cons 797 primesBelow797_perm)

theorem primePrefix809_gt_one : ∀ q ∈ primePrefix809, 1 < q := by
  intro q hq
  rw [primePrefix809] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix797_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive809_811 : ConsecutivePrimes 809 811 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 811. -/
def primePrefix811 : List Nat :=
  809 :: primePrefix809

theorem primesBelow811_perm :
    (primesBelow 811).Perm primePrefix811 := by
  rw [primePrefix811]
  exact consecutive809_811.primesBelow_perm.trans
    (List.Perm.cons 809 primesBelow809_perm)

theorem primePrefix811_gt_one : ∀ q ∈ primePrefix811, 1 < q := by
  intro q hq
  rw [primePrefix811] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix809_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive811_821 : ConsecutivePrimes 811 821 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 821. -/
def primePrefix821 : List Nat :=
  811 :: primePrefix811

theorem primesBelow821_perm :
    (primesBelow 821).Perm primePrefix821 := by
  rw [primePrefix821]
  exact consecutive811_821.primesBelow_perm.trans
    (List.Perm.cons 811 primesBelow811_perm)

theorem primePrefix821_gt_one : ∀ q ∈ primePrefix821, 1 < q := by
  intro q hq
  rw [primePrefix821] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix811_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive821_823 : ConsecutivePrimes 821 823 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 823. -/
def primePrefix823 : List Nat :=
  821 :: primePrefix821

theorem primesBelow823_perm :
    (primesBelow 823).Perm primePrefix823 := by
  rw [primePrefix823]
  exact consecutive821_823.primesBelow_perm.trans
    (List.Perm.cons 821 primesBelow821_perm)

theorem primePrefix823_gt_one : ∀ q ∈ primePrefix823, 1 < q := by
  intro q hq
  rw [primePrefix823] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix821_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive823_827 : ConsecutivePrimes 823 827 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 827. -/
def primePrefix827 : List Nat :=
  823 :: primePrefix823

theorem primesBelow827_perm :
    (primesBelow 827).Perm primePrefix827 := by
  rw [primePrefix827]
  exact consecutive823_827.primesBelow_perm.trans
    (List.Perm.cons 823 primesBelow823_perm)

theorem primePrefix827_gt_one : ∀ q ∈ primePrefix827, 1 < q := by
  intro q hq
  rw [primePrefix827] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix823_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive827_829 : ConsecutivePrimes 827 829 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 829. -/
def primePrefix829 : List Nat :=
  827 :: primePrefix827

theorem primesBelow829_perm :
    (primesBelow 829).Perm primePrefix829 := by
  rw [primePrefix829]
  exact consecutive827_829.primesBelow_perm.trans
    (List.Perm.cons 827 primesBelow827_perm)

theorem primePrefix829_gt_one : ∀ q ∈ primePrefix829, 1 < q := by
  intro q hq
  rw [primePrefix829] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix827_gt_one q hq

end PrimeFactorUnimodality
