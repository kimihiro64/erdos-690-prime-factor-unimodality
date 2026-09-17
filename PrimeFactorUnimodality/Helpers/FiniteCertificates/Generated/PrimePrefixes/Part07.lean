import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes.Part06


set_option autoImplicit false

/-! Generated consecutive-prime chain and reusable exact prime prefixes. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive599_601 : ConsecutivePrimes 599 601 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 601. -/
def primePrefix601 : List Nat :=
  599 :: primePrefix599

theorem primesBelow601_perm :
    (primesBelow 601).Perm primePrefix601 := by
  rw [primePrefix601]
  exact consecutive599_601.primesBelow_perm.trans
    (List.Perm.cons 599 primesBelow599_perm)

theorem primePrefix601_gt_one : ∀ q ∈ primePrefix601, 1 < q := by
  intro q hq
  rw [primePrefix601] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix599_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive601_607 : ConsecutivePrimes 601 607 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 607. -/
def primePrefix607 : List Nat :=
  601 :: primePrefix601

theorem primesBelow607_perm :
    (primesBelow 607).Perm primePrefix607 := by
  rw [primePrefix607]
  exact consecutive601_607.primesBelow_perm.trans
    (List.Perm.cons 601 primesBelow601_perm)

theorem primePrefix607_gt_one : ∀ q ∈ primePrefix607, 1 < q := by
  intro q hq
  rw [primePrefix607] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix601_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive607_613 : ConsecutivePrimes 607 613 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 613. -/
def primePrefix613 : List Nat :=
  607 :: primePrefix607

theorem primesBelow613_perm :
    (primesBelow 613).Perm primePrefix613 := by
  rw [primePrefix613]
  exact consecutive607_613.primesBelow_perm.trans
    (List.Perm.cons 607 primesBelow607_perm)

theorem primePrefix613_gt_one : ∀ q ∈ primePrefix613, 1 < q := by
  intro q hq
  rw [primePrefix613] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix607_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive613_617 : ConsecutivePrimes 613 617 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 617. -/
def primePrefix617 : List Nat :=
  613 :: primePrefix613

theorem primesBelow617_perm :
    (primesBelow 617).Perm primePrefix617 := by
  rw [primePrefix617]
  exact consecutive613_617.primesBelow_perm.trans
    (List.Perm.cons 613 primesBelow613_perm)

theorem primePrefix617_gt_one : ∀ q ∈ primePrefix617, 1 < q := by
  intro q hq
  rw [primePrefix617] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix613_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive617_619 : ConsecutivePrimes 617 619 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 619. -/
def primePrefix619 : List Nat :=
  617 :: primePrefix617

theorem primesBelow619_perm :
    (primesBelow 619).Perm primePrefix619 := by
  rw [primePrefix619]
  exact consecutive617_619.primesBelow_perm.trans
    (List.Perm.cons 617 primesBelow617_perm)

theorem primePrefix619_gt_one : ∀ q ∈ primePrefix619, 1 < q := by
  intro q hq
  rw [primePrefix619] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix617_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive619_631 : ConsecutivePrimes 619 631 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 631. -/
def primePrefix631 : List Nat :=
  619 :: primePrefix619

theorem primesBelow631_perm :
    (primesBelow 631).Perm primePrefix631 := by
  rw [primePrefix631]
  exact consecutive619_631.primesBelow_perm.trans
    (List.Perm.cons 619 primesBelow619_perm)

theorem primePrefix631_gt_one : ∀ q ∈ primePrefix631, 1 < q := by
  intro q hq
  rw [primePrefix631] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix619_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive631_641 : ConsecutivePrimes 631 641 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 641. -/
def primePrefix641 : List Nat :=
  631 :: primePrefix631

theorem primesBelow641_perm :
    (primesBelow 641).Perm primePrefix641 := by
  rw [primePrefix641]
  exact consecutive631_641.primesBelow_perm.trans
    (List.Perm.cons 631 primesBelow631_perm)

theorem primePrefix641_gt_one : ∀ q ∈ primePrefix641, 1 < q := by
  intro q hq
  rw [primePrefix641] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix631_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive641_643 : ConsecutivePrimes 641 643 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 643. -/
def primePrefix643 : List Nat :=
  641 :: primePrefix641

theorem primesBelow643_perm :
    (primesBelow 643).Perm primePrefix643 := by
  rw [primePrefix643]
  exact consecutive641_643.primesBelow_perm.trans
    (List.Perm.cons 641 primesBelow641_perm)

theorem primePrefix643_gt_one : ∀ q ∈ primePrefix643, 1 < q := by
  intro q hq
  rw [primePrefix643] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix641_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive643_647 : ConsecutivePrimes 643 647 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 647. -/
def primePrefix647 : List Nat :=
  643 :: primePrefix643

theorem primesBelow647_perm :
    (primesBelow 647).Perm primePrefix647 := by
  rw [primePrefix647]
  exact consecutive643_647.primesBelow_perm.trans
    (List.Perm.cons 643 primesBelow643_perm)

theorem primePrefix647_gt_one : ∀ q ∈ primePrefix647, 1 < q := by
  intro q hq
  rw [primePrefix647] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix643_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive647_653 : ConsecutivePrimes 647 653 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 653. -/
def primePrefix653 : List Nat :=
  647 :: primePrefix647

theorem primesBelow653_perm :
    (primesBelow 653).Perm primePrefix653 := by
  rw [primePrefix653]
  exact consecutive647_653.primesBelow_perm.trans
    (List.Perm.cons 647 primesBelow647_perm)

theorem primePrefix653_gt_one : ∀ q ∈ primePrefix653, 1 < q := by
  intro q hq
  rw [primePrefix653] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix647_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive653_659 : ConsecutivePrimes 653 659 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 659. -/
def primePrefix659 : List Nat :=
  653 :: primePrefix653

theorem primesBelow659_perm :
    (primesBelow 659).Perm primePrefix659 := by
  rw [primePrefix659]
  exact consecutive653_659.primesBelow_perm.trans
    (List.Perm.cons 653 primesBelow653_perm)

theorem primePrefix659_gt_one : ∀ q ∈ primePrefix659, 1 < q := by
  intro q hq
  rw [primePrefix659] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix653_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive659_661 : ConsecutivePrimes 659 661 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 661. -/
def primePrefix661 : List Nat :=
  659 :: primePrefix659

theorem primesBelow661_perm :
    (primesBelow 661).Perm primePrefix661 := by
  rw [primePrefix661]
  exact consecutive659_661.primesBelow_perm.trans
    (List.Perm.cons 659 primesBelow659_perm)

theorem primePrefix661_gt_one : ∀ q ∈ primePrefix661, 1 < q := by
  intro q hq
  rw [primePrefix661] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix659_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive661_673 : ConsecutivePrimes 661 673 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 673. -/
def primePrefix673 : List Nat :=
  661 :: primePrefix661

theorem primesBelow673_perm :
    (primesBelow 673).Perm primePrefix673 := by
  rw [primePrefix673]
  exact consecutive661_673.primesBelow_perm.trans
    (List.Perm.cons 661 primesBelow661_perm)

theorem primePrefix673_gt_one : ∀ q ∈ primePrefix673, 1 < q := by
  intro q hq
  rw [primePrefix673] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix661_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive673_677 : ConsecutivePrimes 673 677 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 677. -/
def primePrefix677 : List Nat :=
  673 :: primePrefix673

theorem primesBelow677_perm :
    (primesBelow 677).Perm primePrefix677 := by
  rw [primePrefix677]
  exact consecutive673_677.primesBelow_perm.trans
    (List.Perm.cons 673 primesBelow673_perm)

theorem primePrefix677_gt_one : ∀ q ∈ primePrefix677, 1 < q := by
  intro q hq
  rw [primePrefix677] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix673_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive677_683 : ConsecutivePrimes 677 683 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 683. -/
def primePrefix683 : List Nat :=
  677 :: primePrefix677

theorem primesBelow683_perm :
    (primesBelow 683).Perm primePrefix683 := by
  rw [primePrefix683]
  exact consecutive677_683.primesBelow_perm.trans
    (List.Perm.cons 677 primesBelow677_perm)

theorem primePrefix683_gt_one : ∀ q ∈ primePrefix683, 1 < q := by
  intro q hq
  rw [primePrefix683] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix677_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive683_691 : ConsecutivePrimes 683 691 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 691. -/
def primePrefix691 : List Nat :=
  683 :: primePrefix683

theorem primesBelow691_perm :
    (primesBelow 691).Perm primePrefix691 := by
  rw [primePrefix691]
  exact consecutive683_691.primesBelow_perm.trans
    (List.Perm.cons 683 primesBelow683_perm)

theorem primePrefix691_gt_one : ∀ q ∈ primePrefix691, 1 < q := by
  intro q hq
  rw [primePrefix691] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix683_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive691_701 : ConsecutivePrimes 691 701 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 701. -/
def primePrefix701 : List Nat :=
  691 :: primePrefix691

theorem primesBelow701_perm :
    (primesBelow 701).Perm primePrefix701 := by
  rw [primePrefix701]
  exact consecutive691_701.primesBelow_perm.trans
    (List.Perm.cons 691 primesBelow691_perm)

theorem primePrefix701_gt_one : ∀ q ∈ primePrefix701, 1 < q := by
  intro q hq
  rw [primePrefix701] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix691_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive701_709 : ConsecutivePrimes 701 709 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 709. -/
def primePrefix709 : List Nat :=
  701 :: primePrefix701

theorem primesBelow709_perm :
    (primesBelow 709).Perm primePrefix709 := by
  rw [primePrefix709]
  exact consecutive701_709.primesBelow_perm.trans
    (List.Perm.cons 701 primesBelow701_perm)

theorem primePrefix709_gt_one : ∀ q ∈ primePrefix709, 1 < q := by
  intro q hq
  rw [primePrefix709] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix701_gt_one q hq

end PrimeFactorUnimodality
