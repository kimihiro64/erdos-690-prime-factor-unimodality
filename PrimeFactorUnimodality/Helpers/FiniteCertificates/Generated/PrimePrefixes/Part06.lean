import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes.Part05


set_option autoImplicit false

/-! Generated consecutive-prime chain and reusable exact prime prefixes. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive467_479 : ConsecutivePrimes 467 479 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 479. -/
def primePrefix479 : List Nat :=
  467 :: primePrefix467

theorem primesBelow479_perm :
    (primesBelow 479).Perm primePrefix479 := by
  rw [primePrefix479]
  exact consecutive467_479.primesBelow_perm.trans
    (List.Perm.cons 467 primesBelow467_perm)

theorem primePrefix479_gt_one : ∀ q ∈ primePrefix479, 1 < q := by
  intro q hq
  rw [primePrefix479] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix467_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive479_487 : ConsecutivePrimes 479 487 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 487. -/
def primePrefix487 : List Nat :=
  479 :: primePrefix479

theorem primesBelow487_perm :
    (primesBelow 487).Perm primePrefix487 := by
  rw [primePrefix487]
  exact consecutive479_487.primesBelow_perm.trans
    (List.Perm.cons 479 primesBelow479_perm)

theorem primePrefix487_gt_one : ∀ q ∈ primePrefix487, 1 < q := by
  intro q hq
  rw [primePrefix487] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix479_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive487_491 : ConsecutivePrimes 487 491 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 491. -/
def primePrefix491 : List Nat :=
  487 :: primePrefix487

theorem primesBelow491_perm :
    (primesBelow 491).Perm primePrefix491 := by
  rw [primePrefix491]
  exact consecutive487_491.primesBelow_perm.trans
    (List.Perm.cons 487 primesBelow487_perm)

theorem primePrefix491_gt_one : ∀ q ∈ primePrefix491, 1 < q := by
  intro q hq
  rw [primePrefix491] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix487_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive491_499 : ConsecutivePrimes 491 499 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 499. -/
def primePrefix499 : List Nat :=
  491 :: primePrefix491

theorem primesBelow499_perm :
    (primesBelow 499).Perm primePrefix499 := by
  rw [primePrefix499]
  exact consecutive491_499.primesBelow_perm.trans
    (List.Perm.cons 491 primesBelow491_perm)

theorem primePrefix499_gt_one : ∀ q ∈ primePrefix499, 1 < q := by
  intro q hq
  rw [primePrefix499] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix491_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive499_503 : ConsecutivePrimes 499 503 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 503. -/
def primePrefix503 : List Nat :=
  499 :: primePrefix499

theorem primesBelow503_perm :
    (primesBelow 503).Perm primePrefix503 := by
  rw [primePrefix503]
  exact consecutive499_503.primesBelow_perm.trans
    (List.Perm.cons 499 primesBelow499_perm)

theorem primePrefix503_gt_one : ∀ q ∈ primePrefix503, 1 < q := by
  intro q hq
  rw [primePrefix503] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix499_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive503_509 : ConsecutivePrimes 503 509 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 509. -/
def primePrefix509 : List Nat :=
  503 :: primePrefix503

theorem primesBelow509_perm :
    (primesBelow 509).Perm primePrefix509 := by
  rw [primePrefix509]
  exact consecutive503_509.primesBelow_perm.trans
    (List.Perm.cons 503 primesBelow503_perm)

theorem primePrefix509_gt_one : ∀ q ∈ primePrefix509, 1 < q := by
  intro q hq
  rw [primePrefix509] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix503_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive509_521 : ConsecutivePrimes 509 521 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 521. -/
def primePrefix521 : List Nat :=
  509 :: primePrefix509

theorem primesBelow521_perm :
    (primesBelow 521).Perm primePrefix521 := by
  rw [primePrefix521]
  exact consecutive509_521.primesBelow_perm.trans
    (List.Perm.cons 509 primesBelow509_perm)

theorem primePrefix521_gt_one : ∀ q ∈ primePrefix521, 1 < q := by
  intro q hq
  rw [primePrefix521] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix509_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive521_523 : ConsecutivePrimes 521 523 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 523. -/
def primePrefix523 : List Nat :=
  521 :: primePrefix521

theorem primesBelow523_perm :
    (primesBelow 523).Perm primePrefix523 := by
  rw [primePrefix523]
  exact consecutive521_523.primesBelow_perm.trans
    (List.Perm.cons 521 primesBelow521_perm)

theorem primePrefix523_gt_one : ∀ q ∈ primePrefix523, 1 < q := by
  intro q hq
  rw [primePrefix523] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix521_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive523_541 : ConsecutivePrimes 523 541 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 541. -/
def primePrefix541 : List Nat :=
  523 :: primePrefix523

theorem primesBelow541_perm :
    (primesBelow 541).Perm primePrefix541 := by
  rw [primePrefix541]
  exact consecutive523_541.primesBelow_perm.trans
    (List.Perm.cons 523 primesBelow523_perm)

theorem primePrefix541_gt_one : ∀ q ∈ primePrefix541, 1 < q := by
  intro q hq
  rw [primePrefix541] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix523_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive541_547 : ConsecutivePrimes 541 547 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 547. -/
def primePrefix547 : List Nat :=
  541 :: primePrefix541

theorem primesBelow547_perm :
    (primesBelow 547).Perm primePrefix547 := by
  rw [primePrefix547]
  exact consecutive541_547.primesBelow_perm.trans
    (List.Perm.cons 541 primesBelow541_perm)

theorem primePrefix547_gt_one : ∀ q ∈ primePrefix547, 1 < q := by
  intro q hq
  rw [primePrefix547] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix541_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive547_557 : ConsecutivePrimes 547 557 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 557. -/
def primePrefix557 : List Nat :=
  547 :: primePrefix547

theorem primesBelow557_perm :
    (primesBelow 557).Perm primePrefix557 := by
  rw [primePrefix557]
  exact consecutive547_557.primesBelow_perm.trans
    (List.Perm.cons 547 primesBelow547_perm)

theorem primePrefix557_gt_one : ∀ q ∈ primePrefix557, 1 < q := by
  intro q hq
  rw [primePrefix557] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix547_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive557_563 : ConsecutivePrimes 557 563 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 563. -/
def primePrefix563 : List Nat :=
  557 :: primePrefix557

theorem primesBelow563_perm :
    (primesBelow 563).Perm primePrefix563 := by
  rw [primePrefix563]
  exact consecutive557_563.primesBelow_perm.trans
    (List.Perm.cons 557 primesBelow557_perm)

theorem primePrefix563_gt_one : ∀ q ∈ primePrefix563, 1 < q := by
  intro q hq
  rw [primePrefix563] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix557_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive563_569 : ConsecutivePrimes 563 569 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 569. -/
def primePrefix569 : List Nat :=
  563 :: primePrefix563

theorem primesBelow569_perm :
    (primesBelow 569).Perm primePrefix569 := by
  rw [primePrefix569]
  exact consecutive563_569.primesBelow_perm.trans
    (List.Perm.cons 563 primesBelow563_perm)

theorem primePrefix569_gt_one : ∀ q ∈ primePrefix569, 1 < q := by
  intro q hq
  rw [primePrefix569] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix563_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive569_571 : ConsecutivePrimes 569 571 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 571. -/
def primePrefix571 : List Nat :=
  569 :: primePrefix569

theorem primesBelow571_perm :
    (primesBelow 571).Perm primePrefix571 := by
  rw [primePrefix571]
  exact consecutive569_571.primesBelow_perm.trans
    (List.Perm.cons 569 primesBelow569_perm)

theorem primePrefix571_gt_one : ∀ q ∈ primePrefix571, 1 < q := by
  intro q hq
  rw [primePrefix571] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix569_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive571_577 : ConsecutivePrimes 571 577 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 577. -/
def primePrefix577 : List Nat :=
  571 :: primePrefix571

theorem primesBelow577_perm :
    (primesBelow 577).Perm primePrefix577 := by
  rw [primePrefix577]
  exact consecutive571_577.primesBelow_perm.trans
    (List.Perm.cons 571 primesBelow571_perm)

theorem primePrefix577_gt_one : ∀ q ∈ primePrefix577, 1 < q := by
  intro q hq
  rw [primePrefix577] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix571_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive577_587 : ConsecutivePrimes 577 587 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 587. -/
def primePrefix587 : List Nat :=
  577 :: primePrefix577

theorem primesBelow587_perm :
    (primesBelow 587).Perm primePrefix587 := by
  rw [primePrefix587]
  exact consecutive577_587.primesBelow_perm.trans
    (List.Perm.cons 577 primesBelow577_perm)

theorem primePrefix587_gt_one : ∀ q ∈ primePrefix587, 1 < q := by
  intro q hq
  rw [primePrefix587] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix577_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive587_593 : ConsecutivePrimes 587 593 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 593. -/
def primePrefix593 : List Nat :=
  587 :: primePrefix587

theorem primesBelow593_perm :
    (primesBelow 593).Perm primePrefix593 := by
  rw [primePrefix593]
  exact consecutive587_593.primesBelow_perm.trans
    (List.Perm.cons 587 primesBelow587_perm)

theorem primePrefix593_gt_one : ∀ q ∈ primePrefix593, 1 < q := by
  intro q hq
  rw [primePrefix593] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix587_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive593_599 : ConsecutivePrimes 593 599 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 599. -/
def primePrefix599 : List Nat :=
  593 :: primePrefix593

theorem primesBelow599_perm :
    (primesBelow 599).Perm primePrefix599 := by
  rw [primePrefix599]
  exact consecutive593_599.primesBelow_perm.trans
    (List.Perm.cons 593 primesBelow593_perm)

theorem primePrefix599_gt_one : ∀ q ∈ primePrefix599, 1 < q := by
  intro q hq
  rw [primePrefix599] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix593_gt_one q hq

end PrimeFactorUnimodality
