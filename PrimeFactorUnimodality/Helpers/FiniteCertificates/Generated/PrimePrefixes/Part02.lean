import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes.Part01


set_option autoImplicit false

/-! Generated consecutive-prime chain and reusable exact prime prefixes. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive67_71 : ConsecutivePrimes 67 71 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 71. -/
def primePrefix71 : List Nat :=
  67 :: primePrefix67

theorem primesBelow71_perm :
    (primesBelow 71).Perm primePrefix71 := by
  rw [primePrefix71]
  exact consecutive67_71.primesBelow_perm.trans
    (List.Perm.cons 67 primesBelow67_perm)

theorem primePrefix71_gt_one : ∀ q ∈ primePrefix71, 1 < q := by
  intro q hq
  rw [primePrefix71] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix67_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive71_73 : ConsecutivePrimes 71 73 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 73. -/
def primePrefix73 : List Nat :=
  71 :: primePrefix71

theorem primesBelow73_perm :
    (primesBelow 73).Perm primePrefix73 := by
  rw [primePrefix73]
  exact consecutive71_73.primesBelow_perm.trans
    (List.Perm.cons 71 primesBelow71_perm)

theorem primePrefix73_gt_one : ∀ q ∈ primePrefix73, 1 < q := by
  intro q hq
  rw [primePrefix73] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix71_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive73_79 : ConsecutivePrimes 73 79 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 79. -/
def primePrefix79 : List Nat :=
  73 :: primePrefix73

theorem primesBelow79_perm :
    (primesBelow 79).Perm primePrefix79 := by
  rw [primePrefix79]
  exact consecutive73_79.primesBelow_perm.trans
    (List.Perm.cons 73 primesBelow73_perm)

theorem primePrefix79_gt_one : ∀ q ∈ primePrefix79, 1 < q := by
  intro q hq
  rw [primePrefix79] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix73_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive79_83 : ConsecutivePrimes 79 83 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 83. -/
def primePrefix83 : List Nat :=
  79 :: primePrefix79

theorem primesBelow83_perm :
    (primesBelow 83).Perm primePrefix83 := by
  rw [primePrefix83]
  exact consecutive79_83.primesBelow_perm.trans
    (List.Perm.cons 79 primesBelow79_perm)

theorem primePrefix83_gt_one : ∀ q ∈ primePrefix83, 1 < q := by
  intro q hq
  rw [primePrefix83] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix79_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive83_89 : ConsecutivePrimes 83 89 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 89. -/
def primePrefix89 : List Nat :=
  83 :: primePrefix83

theorem primesBelow89_perm :
    (primesBelow 89).Perm primePrefix89 := by
  rw [primePrefix89]
  exact consecutive83_89.primesBelow_perm.trans
    (List.Perm.cons 83 primesBelow83_perm)

theorem primePrefix89_gt_one : ∀ q ∈ primePrefix89, 1 < q := by
  intro q hq
  rw [primePrefix89] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix83_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive89_97 : ConsecutivePrimes 89 97 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 97. -/
def primePrefix97 : List Nat :=
  89 :: primePrefix89

theorem primesBelow97_perm :
    (primesBelow 97).Perm primePrefix97 := by
  rw [primePrefix97]
  exact consecutive89_97.primesBelow_perm.trans
    (List.Perm.cons 89 primesBelow89_perm)

theorem primePrefix97_gt_one : ∀ q ∈ primePrefix97, 1 < q := by
  intro q hq
  rw [primePrefix97] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix89_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive97_101 : ConsecutivePrimes 97 101 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 101. -/
def primePrefix101 : List Nat :=
  97 :: primePrefix97

theorem primesBelow101_perm :
    (primesBelow 101).Perm primePrefix101 := by
  rw [primePrefix101]
  exact consecutive97_101.primesBelow_perm.trans
    (List.Perm.cons 97 primesBelow97_perm)

theorem primePrefix101_gt_one : ∀ q ∈ primePrefix101, 1 < q := by
  intro q hq
  rw [primePrefix101] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix97_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive101_103 : ConsecutivePrimes 101 103 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 103. -/
def primePrefix103 : List Nat :=
  101 :: primePrefix101

theorem primesBelow103_perm :
    (primesBelow 103).Perm primePrefix103 := by
  rw [primePrefix103]
  exact consecutive101_103.primesBelow_perm.trans
    (List.Perm.cons 101 primesBelow101_perm)

theorem primePrefix103_gt_one : ∀ q ∈ primePrefix103, 1 < q := by
  intro q hq
  rw [primePrefix103] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix101_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive103_107 : ConsecutivePrimes 103 107 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 107. -/
def primePrefix107 : List Nat :=
  103 :: primePrefix103

theorem primesBelow107_perm :
    (primesBelow 107).Perm primePrefix107 := by
  rw [primePrefix107]
  exact consecutive103_107.primesBelow_perm.trans
    (List.Perm.cons 103 primesBelow103_perm)

theorem primePrefix107_gt_one : ∀ q ∈ primePrefix107, 1 < q := by
  intro q hq
  rw [primePrefix107] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix103_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive107_109 : ConsecutivePrimes 107 109 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 109. -/
def primePrefix109 : List Nat :=
  107 :: primePrefix107

theorem primesBelow109_perm :
    (primesBelow 109).Perm primePrefix109 := by
  rw [primePrefix109]
  exact consecutive107_109.primesBelow_perm.trans
    (List.Perm.cons 107 primesBelow107_perm)

theorem primePrefix109_gt_one : ∀ q ∈ primePrefix109, 1 < q := by
  intro q hq
  rw [primePrefix109] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix107_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive109_113 : ConsecutivePrimes 109 113 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 113. -/
def primePrefix113 : List Nat :=
  109 :: primePrefix109

theorem primesBelow113_perm :
    (primesBelow 113).Perm primePrefix113 := by
  rw [primePrefix113]
  exact consecutive109_113.primesBelow_perm.trans
    (List.Perm.cons 109 primesBelow109_perm)

theorem primePrefix113_gt_one : ∀ q ∈ primePrefix113, 1 < q := by
  intro q hq
  rw [primePrefix113] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix109_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive113_127 : ConsecutivePrimes 113 127 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 127. -/
def primePrefix127 : List Nat :=
  113 :: primePrefix113

theorem primesBelow127_perm :
    (primesBelow 127).Perm primePrefix127 := by
  rw [primePrefix127]
  exact consecutive113_127.primesBelow_perm.trans
    (List.Perm.cons 113 primesBelow113_perm)

theorem primePrefix127_gt_one : ∀ q ∈ primePrefix127, 1 < q := by
  intro q hq
  rw [primePrefix127] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix113_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive127_131 : ConsecutivePrimes 127 131 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 131. -/
def primePrefix131 : List Nat :=
  127 :: primePrefix127

theorem primesBelow131_perm :
    (primesBelow 131).Perm primePrefix131 := by
  rw [primePrefix131]
  exact consecutive127_131.primesBelow_perm.trans
    (List.Perm.cons 127 primesBelow127_perm)

theorem primePrefix131_gt_one : ∀ q ∈ primePrefix131, 1 < q := by
  intro q hq
  rw [primePrefix131] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix127_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive131_137 : ConsecutivePrimes 131 137 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 137. -/
def primePrefix137 : List Nat :=
  131 :: primePrefix131

theorem primesBelow137_perm :
    (primesBelow 137).Perm primePrefix137 := by
  rw [primePrefix137]
  exact consecutive131_137.primesBelow_perm.trans
    (List.Perm.cons 131 primesBelow131_perm)

theorem primePrefix137_gt_one : ∀ q ∈ primePrefix137, 1 < q := by
  intro q hq
  rw [primePrefix137] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix131_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive137_139 : ConsecutivePrimes 137 139 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 139. -/
def primePrefix139 : List Nat :=
  137 :: primePrefix137

theorem primesBelow139_perm :
    (primesBelow 139).Perm primePrefix139 := by
  rw [primePrefix139]
  exact consecutive137_139.primesBelow_perm.trans
    (List.Perm.cons 137 primesBelow137_perm)

theorem primePrefix139_gt_one : ∀ q ∈ primePrefix139, 1 < q := by
  intro q hq
  rw [primePrefix139] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix137_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive139_149 : ConsecutivePrimes 139 149 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 149. -/
def primePrefix149 : List Nat :=
  139 :: primePrefix139

theorem primesBelow149_perm :
    (primesBelow 149).Perm primePrefix149 := by
  rw [primePrefix149]
  exact consecutive139_149.primesBelow_perm.trans
    (List.Perm.cons 139 primesBelow139_perm)

theorem primePrefix149_gt_one : ∀ q ∈ primePrefix149, 1 < q := by
  intro q hq
  rw [primePrefix149] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix139_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive149_151 : ConsecutivePrimes 149 151 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 151. -/
def primePrefix151 : List Nat :=
  149 :: primePrefix149

theorem primesBelow151_perm :
    (primesBelow 151).Perm primePrefix151 := by
  rw [primePrefix151]
  exact consecutive149_151.primesBelow_perm.trans
    (List.Perm.cons 149 primesBelow149_perm)

theorem primePrefix151_gt_one : ∀ q ∈ primePrefix151, 1 < q := by
  intro q hq
  rw [primePrefix151] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix149_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive151_157 : ConsecutivePrimes 151 157 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 157. -/
def primePrefix157 : List Nat :=
  151 :: primePrefix151

theorem primesBelow157_perm :
    (primesBelow 157).Perm primePrefix157 := by
  rw [primePrefix157]
  exact consecutive151_157.primesBelow_perm.trans
    (List.Perm.cons 151 primesBelow151_perm)

theorem primePrefix157_gt_one : ∀ q ∈ primePrefix157, 1 < q := by
  intro q hq
  rw [primePrefix157] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix151_gt_one q hq

end PrimeFactorUnimodality
