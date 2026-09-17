import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes.Part10


set_option autoImplicit false

/-! Generated consecutive-prime chain and reusable exact prime prefixes. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1087_1091 : ConsecutivePrimes 1087 1091 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1091. -/
def primePrefix1091 : List Nat :=
  1087 :: primePrefix1087

theorem primesBelow1091_perm :
    (primesBelow 1091).Perm primePrefix1091 := by
  rw [primePrefix1091]
  exact consecutive1087_1091.primesBelow_perm.trans
    (List.Perm.cons 1087 primesBelow1087_perm)

theorem primePrefix1091_gt_one : ∀ q ∈ primePrefix1091, 1 < q := by
  intro q hq
  rw [primePrefix1091] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1087_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1091_1093 : ConsecutivePrimes 1091 1093 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1093. -/
def primePrefix1093 : List Nat :=
  1091 :: primePrefix1091

theorem primesBelow1093_perm :
    (primesBelow 1093).Perm primePrefix1093 := by
  rw [primePrefix1093]
  exact consecutive1091_1093.primesBelow_perm.trans
    (List.Perm.cons 1091 primesBelow1091_perm)

theorem primePrefix1093_gt_one : ∀ q ∈ primePrefix1093, 1 < q := by
  intro q hq
  rw [primePrefix1093] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1091_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1093_1097 : ConsecutivePrimes 1093 1097 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1097. -/
def primePrefix1097 : List Nat :=
  1093 :: primePrefix1093

theorem primesBelow1097_perm :
    (primesBelow 1097).Perm primePrefix1097 := by
  rw [primePrefix1097]
  exact consecutive1093_1097.primesBelow_perm.trans
    (List.Perm.cons 1093 primesBelow1093_perm)

theorem primePrefix1097_gt_one : ∀ q ∈ primePrefix1097, 1 < q := by
  intro q hq
  rw [primePrefix1097] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1093_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1097_1103 : ConsecutivePrimes 1097 1103 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1103. -/
def primePrefix1103 : List Nat :=
  1097 :: primePrefix1097

theorem primesBelow1103_perm :
    (primesBelow 1103).Perm primePrefix1103 := by
  rw [primePrefix1103]
  exact consecutive1097_1103.primesBelow_perm.trans
    (List.Perm.cons 1097 primesBelow1097_perm)

theorem primePrefix1103_gt_one : ∀ q ∈ primePrefix1103, 1 < q := by
  intro q hq
  rw [primePrefix1103] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1097_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1103_1109 : ConsecutivePrimes 1103 1109 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1109. -/
def primePrefix1109 : List Nat :=
  1103 :: primePrefix1103

theorem primesBelow1109_perm :
    (primesBelow 1109).Perm primePrefix1109 := by
  rw [primePrefix1109]
  exact consecutive1103_1109.primesBelow_perm.trans
    (List.Perm.cons 1103 primesBelow1103_perm)

theorem primePrefix1109_gt_one : ∀ q ∈ primePrefix1109, 1 < q := by
  intro q hq
  rw [primePrefix1109] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1103_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1109_1117 : ConsecutivePrimes 1109 1117 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1117. -/
def primePrefix1117 : List Nat :=
  1109 :: primePrefix1109

theorem primesBelow1117_perm :
    (primesBelow 1117).Perm primePrefix1117 := by
  rw [primePrefix1117]
  exact consecutive1109_1117.primesBelow_perm.trans
    (List.Perm.cons 1109 primesBelow1109_perm)

theorem primePrefix1117_gt_one : ∀ q ∈ primePrefix1117, 1 < q := by
  intro q hq
  rw [primePrefix1117] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1109_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1117_1123 : ConsecutivePrimes 1117 1123 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1123. -/
def primePrefix1123 : List Nat :=
  1117 :: primePrefix1117

theorem primesBelow1123_perm :
    (primesBelow 1123).Perm primePrefix1123 := by
  rw [primePrefix1123]
  exact consecutive1117_1123.primesBelow_perm.trans
    (List.Perm.cons 1117 primesBelow1117_perm)

theorem primePrefix1123_gt_one : ∀ q ∈ primePrefix1123, 1 < q := by
  intro q hq
  rw [primePrefix1123] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1117_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1123_1129 : ConsecutivePrimes 1123 1129 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1129. -/
def primePrefix1129 : List Nat :=
  1123 :: primePrefix1123

theorem primesBelow1129_perm :
    (primesBelow 1129).Perm primePrefix1129 := by
  rw [primePrefix1129]
  exact consecutive1123_1129.primesBelow_perm.trans
    (List.Perm.cons 1123 primesBelow1123_perm)

theorem primePrefix1129_gt_one : ∀ q ∈ primePrefix1129, 1 < q := by
  intro q hq
  rw [primePrefix1129] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1123_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1129_1151 : ConsecutivePrimes 1129 1151 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1151. -/
def primePrefix1151 : List Nat :=
  1129 :: primePrefix1129

theorem primesBelow1151_perm :
    (primesBelow 1151).Perm primePrefix1151 := by
  rw [primePrefix1151]
  exact consecutive1129_1151.primesBelow_perm.trans
    (List.Perm.cons 1129 primesBelow1129_perm)

theorem primePrefix1151_gt_one : ∀ q ∈ primePrefix1151, 1 < q := by
  intro q hq
  rw [primePrefix1151] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1129_gt_one q hq

end PrimeFactorUnimodality
