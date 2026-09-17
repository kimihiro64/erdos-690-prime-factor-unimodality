import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes.Part04


set_option autoImplicit false

/-! Generated consecutive-prime chain and reusable exact prime prefixes. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive367_373 : ConsecutivePrimes 367 373 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 373. -/
def primePrefix373 : List Nat :=
  367 :: primePrefix367

theorem primesBelow373_perm :
    (primesBelow 373).Perm primePrefix373 := by
  rw [primePrefix373]
  exact consecutive367_373.primesBelow_perm.trans
    (List.Perm.cons 367 primesBelow367_perm)

theorem primePrefix373_gt_one : ∀ q ∈ primePrefix373, 1 < q := by
  intro q hq
  rw [primePrefix373] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix367_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive373_379 : ConsecutivePrimes 373 379 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 379. -/
def primePrefix379 : List Nat :=
  373 :: primePrefix373

theorem primesBelow379_perm :
    (primesBelow 379).Perm primePrefix379 := by
  rw [primePrefix379]
  exact consecutive373_379.primesBelow_perm.trans
    (List.Perm.cons 373 primesBelow373_perm)

theorem primePrefix379_gt_one : ∀ q ∈ primePrefix379, 1 < q := by
  intro q hq
  rw [primePrefix379] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix373_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive379_383 : ConsecutivePrimes 379 383 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 383. -/
def primePrefix383 : List Nat :=
  379 :: primePrefix379

theorem primesBelow383_perm :
    (primesBelow 383).Perm primePrefix383 := by
  rw [primePrefix383]
  exact consecutive379_383.primesBelow_perm.trans
    (List.Perm.cons 379 primesBelow379_perm)

theorem primePrefix383_gt_one : ∀ q ∈ primePrefix383, 1 < q := by
  intro q hq
  rw [primePrefix383] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix379_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive383_389 : ConsecutivePrimes 383 389 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 389. -/
def primePrefix389 : List Nat :=
  383 :: primePrefix383

theorem primesBelow389_perm :
    (primesBelow 389).Perm primePrefix389 := by
  rw [primePrefix389]
  exact consecutive383_389.primesBelow_perm.trans
    (List.Perm.cons 383 primesBelow383_perm)

theorem primePrefix389_gt_one : ∀ q ∈ primePrefix389, 1 < q := by
  intro q hq
  rw [primePrefix389] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix383_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive389_397 : ConsecutivePrimes 389 397 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 397. -/
def primePrefix397 : List Nat :=
  389 :: primePrefix389

theorem primesBelow397_perm :
    (primesBelow 397).Perm primePrefix397 := by
  rw [primePrefix397]
  exact consecutive389_397.primesBelow_perm.trans
    (List.Perm.cons 389 primesBelow389_perm)

theorem primePrefix397_gt_one : ∀ q ∈ primePrefix397, 1 < q := by
  intro q hq
  rw [primePrefix397] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix389_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive397_401 : ConsecutivePrimes 397 401 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 401. -/
def primePrefix401 : List Nat :=
  397 :: primePrefix397

theorem primesBelow401_perm :
    (primesBelow 401).Perm primePrefix401 := by
  rw [primePrefix401]
  exact consecutive397_401.primesBelow_perm.trans
    (List.Perm.cons 397 primesBelow397_perm)

theorem primePrefix401_gt_one : ∀ q ∈ primePrefix401, 1 < q := by
  intro q hq
  rw [primePrefix401] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix397_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive401_409 : ConsecutivePrimes 401 409 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 409. -/
def primePrefix409 : List Nat :=
  401 :: primePrefix401

theorem primesBelow409_perm :
    (primesBelow 409).Perm primePrefix409 := by
  rw [primePrefix409]
  exact consecutive401_409.primesBelow_perm.trans
    (List.Perm.cons 401 primesBelow401_perm)

theorem primePrefix409_gt_one : ∀ q ∈ primePrefix409, 1 < q := by
  intro q hq
  rw [primePrefix409] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix401_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive409_419 : ConsecutivePrimes 409 419 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 419. -/
def primePrefix419 : List Nat :=
  409 :: primePrefix409

theorem primesBelow419_perm :
    (primesBelow 419).Perm primePrefix419 := by
  rw [primePrefix419]
  exact consecutive409_419.primesBelow_perm.trans
    (List.Perm.cons 409 primesBelow409_perm)

theorem primePrefix419_gt_one : ∀ q ∈ primePrefix419, 1 < q := by
  intro q hq
  rw [primePrefix419] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix409_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive419_421 : ConsecutivePrimes 419 421 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 421. -/
def primePrefix421 : List Nat :=
  419 :: primePrefix419

theorem primesBelow421_perm :
    (primesBelow 421).Perm primePrefix421 := by
  rw [primePrefix421]
  exact consecutive419_421.primesBelow_perm.trans
    (List.Perm.cons 419 primesBelow419_perm)

theorem primePrefix421_gt_one : ∀ q ∈ primePrefix421, 1 < q := by
  intro q hq
  rw [primePrefix421] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix419_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive421_431 : ConsecutivePrimes 421 431 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 431. -/
def primePrefix431 : List Nat :=
  421 :: primePrefix421

theorem primesBelow431_perm :
    (primesBelow 431).Perm primePrefix431 := by
  rw [primePrefix431]
  exact consecutive421_431.primesBelow_perm.trans
    (List.Perm.cons 421 primesBelow421_perm)

theorem primePrefix431_gt_one : ∀ q ∈ primePrefix431, 1 < q := by
  intro q hq
  rw [primePrefix431] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix421_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive431_433 : ConsecutivePrimes 431 433 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 433. -/
def primePrefix433 : List Nat :=
  431 :: primePrefix431

theorem primesBelow433_perm :
    (primesBelow 433).Perm primePrefix433 := by
  rw [primePrefix433]
  exact consecutive431_433.primesBelow_perm.trans
    (List.Perm.cons 431 primesBelow431_perm)

theorem primePrefix433_gt_one : ∀ q ∈ primePrefix433, 1 < q := by
  intro q hq
  rw [primePrefix433] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix431_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive433_439 : ConsecutivePrimes 433 439 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 439. -/
def primePrefix439 : List Nat :=
  433 :: primePrefix433

theorem primesBelow439_perm :
    (primesBelow 439).Perm primePrefix439 := by
  rw [primePrefix439]
  exact consecutive433_439.primesBelow_perm.trans
    (List.Perm.cons 433 primesBelow433_perm)

theorem primePrefix439_gt_one : ∀ q ∈ primePrefix439, 1 < q := by
  intro q hq
  rw [primePrefix439] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix433_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive439_443 : ConsecutivePrimes 439 443 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 443. -/
def primePrefix443 : List Nat :=
  439 :: primePrefix439

theorem primesBelow443_perm :
    (primesBelow 443).Perm primePrefix443 := by
  rw [primePrefix443]
  exact consecutive439_443.primesBelow_perm.trans
    (List.Perm.cons 439 primesBelow439_perm)

theorem primePrefix443_gt_one : ∀ q ∈ primePrefix443, 1 < q := by
  intro q hq
  rw [primePrefix443] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix439_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive443_449 : ConsecutivePrimes 443 449 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 449. -/
def primePrefix449 : List Nat :=
  443 :: primePrefix443

theorem primesBelow449_perm :
    (primesBelow 449).Perm primePrefix449 := by
  rw [primePrefix449]
  exact consecutive443_449.primesBelow_perm.trans
    (List.Perm.cons 443 primesBelow443_perm)

theorem primePrefix449_gt_one : ∀ q ∈ primePrefix449, 1 < q := by
  intro q hq
  rw [primePrefix449] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix443_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive449_457 : ConsecutivePrimes 449 457 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 457. -/
def primePrefix457 : List Nat :=
  449 :: primePrefix449

theorem primesBelow457_perm :
    (primesBelow 457).Perm primePrefix457 := by
  rw [primePrefix457]
  exact consecutive449_457.primesBelow_perm.trans
    (List.Perm.cons 449 primesBelow449_perm)

theorem primePrefix457_gt_one : ∀ q ∈ primePrefix457, 1 < q := by
  intro q hq
  rw [primePrefix457] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix449_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive457_461 : ConsecutivePrimes 457 461 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 461. -/
def primePrefix461 : List Nat :=
  457 :: primePrefix457

theorem primesBelow461_perm :
    (primesBelow 461).Perm primePrefix461 := by
  rw [primePrefix461]
  exact consecutive457_461.primesBelow_perm.trans
    (List.Perm.cons 457 primesBelow457_perm)

theorem primePrefix461_gt_one : ∀ q ∈ primePrefix461, 1 < q := by
  intro q hq
  rw [primePrefix461] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix457_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive461_463 : ConsecutivePrimes 461 463 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 463. -/
def primePrefix463 : List Nat :=
  461 :: primePrefix461

theorem primesBelow463_perm :
    (primesBelow 463).Perm primePrefix463 := by
  rw [primePrefix463]
  exact consecutive461_463.primesBelow_perm.trans
    (List.Perm.cons 461 primesBelow461_perm)

theorem primePrefix463_gt_one : ∀ q ∈ primePrefix463, 1 < q := by
  intro q hq
  rw [primePrefix463] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix461_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive463_467 : ConsecutivePrimes 463 467 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 467. -/
def primePrefix467 : List Nat :=
  463 :: primePrefix463

theorem primesBelow467_perm :
    (primesBelow 467).Perm primePrefix467 := by
  rw [primePrefix467]
  exact consecutive463_467.primesBelow_perm.trans
    (List.Perm.cons 463 primesBelow463_perm)

theorem primePrefix467_gt_one : ∀ q ∈ primePrefix467, 1 < q := by
  intro q hq
  rw [primePrefix467] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix463_gt_one q hq

end PrimeFactorUnimodality
