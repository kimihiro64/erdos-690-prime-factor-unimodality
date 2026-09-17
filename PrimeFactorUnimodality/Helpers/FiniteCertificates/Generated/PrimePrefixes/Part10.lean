import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes.Part09


set_option autoImplicit false

/-! Generated consecutive-prime chain and reusable exact prime prefixes. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive967_971 : ConsecutivePrimes 967 971 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 971. -/
def primePrefix971 : List Nat :=
  967 :: primePrefix967

theorem primesBelow971_perm :
    (primesBelow 971).Perm primePrefix971 := by
  rw [primePrefix971]
  exact consecutive967_971.primesBelow_perm.trans
    (List.Perm.cons 967 primesBelow967_perm)

theorem primePrefix971_gt_one : ∀ q ∈ primePrefix971, 1 < q := by
  intro q hq
  rw [primePrefix971] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix967_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive971_977 : ConsecutivePrimes 971 977 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 977. -/
def primePrefix977 : List Nat :=
  971 :: primePrefix971

theorem primesBelow977_perm :
    (primesBelow 977).Perm primePrefix977 := by
  rw [primePrefix977]
  exact consecutive971_977.primesBelow_perm.trans
    (List.Perm.cons 971 primesBelow971_perm)

theorem primePrefix977_gt_one : ∀ q ∈ primePrefix977, 1 < q := by
  intro q hq
  rw [primePrefix977] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix971_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive977_983 : ConsecutivePrimes 977 983 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 983. -/
def primePrefix983 : List Nat :=
  977 :: primePrefix977

theorem primesBelow983_perm :
    (primesBelow 983).Perm primePrefix983 := by
  rw [primePrefix983]
  exact consecutive977_983.primesBelow_perm.trans
    (List.Perm.cons 977 primesBelow977_perm)

theorem primePrefix983_gt_one : ∀ q ∈ primePrefix983, 1 < q := by
  intro q hq
  rw [primePrefix983] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix977_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive983_991 : ConsecutivePrimes 983 991 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 991. -/
def primePrefix991 : List Nat :=
  983 :: primePrefix983

theorem primesBelow991_perm :
    (primesBelow 991).Perm primePrefix991 := by
  rw [primePrefix991]
  exact consecutive983_991.primesBelow_perm.trans
    (List.Perm.cons 983 primesBelow983_perm)

theorem primePrefix991_gt_one : ∀ q ∈ primePrefix991, 1 < q := by
  intro q hq
  rw [primePrefix991] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix983_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive991_997 : ConsecutivePrimes 991 997 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 997. -/
def primePrefix997 : List Nat :=
  991 :: primePrefix991

theorem primesBelow997_perm :
    (primesBelow 997).Perm primePrefix997 := by
  rw [primePrefix997]
  exact consecutive991_997.primesBelow_perm.trans
    (List.Perm.cons 991 primesBelow991_perm)

theorem primePrefix997_gt_one : ∀ q ∈ primePrefix997, 1 < q := by
  intro q hq
  rw [primePrefix997] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix991_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive997_1009 : ConsecutivePrimes 997 1009 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1009. -/
def primePrefix1009 : List Nat :=
  997 :: primePrefix997

theorem primesBelow1009_perm :
    (primesBelow 1009).Perm primePrefix1009 := by
  rw [primePrefix1009]
  exact consecutive997_1009.primesBelow_perm.trans
    (List.Perm.cons 997 primesBelow997_perm)

theorem primePrefix1009_gt_one : ∀ q ∈ primePrefix1009, 1 < q := by
  intro q hq
  rw [primePrefix1009] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix997_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1009_1013 : ConsecutivePrimes 1009 1013 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1013. -/
def primePrefix1013 : List Nat :=
  1009 :: primePrefix1009

theorem primesBelow1013_perm :
    (primesBelow 1013).Perm primePrefix1013 := by
  rw [primePrefix1013]
  exact consecutive1009_1013.primesBelow_perm.trans
    (List.Perm.cons 1009 primesBelow1009_perm)

theorem primePrefix1013_gt_one : ∀ q ∈ primePrefix1013, 1 < q := by
  intro q hq
  rw [primePrefix1013] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1009_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1013_1019 : ConsecutivePrimes 1013 1019 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1019. -/
def primePrefix1019 : List Nat :=
  1013 :: primePrefix1013

theorem primesBelow1019_perm :
    (primesBelow 1019).Perm primePrefix1019 := by
  rw [primePrefix1019]
  exact consecutive1013_1019.primesBelow_perm.trans
    (List.Perm.cons 1013 primesBelow1013_perm)

theorem primePrefix1019_gt_one : ∀ q ∈ primePrefix1019, 1 < q := by
  intro q hq
  rw [primePrefix1019] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1013_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1019_1021 : ConsecutivePrimes 1019 1021 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1021. -/
def primePrefix1021 : List Nat :=
  1019 :: primePrefix1019

theorem primesBelow1021_perm :
    (primesBelow 1021).Perm primePrefix1021 := by
  rw [primePrefix1021]
  exact consecutive1019_1021.primesBelow_perm.trans
    (List.Perm.cons 1019 primesBelow1019_perm)

theorem primePrefix1021_gt_one : ∀ q ∈ primePrefix1021, 1 < q := by
  intro q hq
  rw [primePrefix1021] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1019_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1021_1031 : ConsecutivePrimes 1021 1031 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1031. -/
def primePrefix1031 : List Nat :=
  1021 :: primePrefix1021

theorem primesBelow1031_perm :
    (primesBelow 1031).Perm primePrefix1031 := by
  rw [primePrefix1031]
  exact consecutive1021_1031.primesBelow_perm.trans
    (List.Perm.cons 1021 primesBelow1021_perm)

theorem primePrefix1031_gt_one : ∀ q ∈ primePrefix1031, 1 < q := by
  intro q hq
  rw [primePrefix1031] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1021_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1031_1033 : ConsecutivePrimes 1031 1033 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1033. -/
def primePrefix1033 : List Nat :=
  1031 :: primePrefix1031

theorem primesBelow1033_perm :
    (primesBelow 1033).Perm primePrefix1033 := by
  rw [primePrefix1033]
  exact consecutive1031_1033.primesBelow_perm.trans
    (List.Perm.cons 1031 primesBelow1031_perm)

theorem primePrefix1033_gt_one : ∀ q ∈ primePrefix1033, 1 < q := by
  intro q hq
  rw [primePrefix1033] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1031_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1033_1039 : ConsecutivePrimes 1033 1039 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1039. -/
def primePrefix1039 : List Nat :=
  1033 :: primePrefix1033

theorem primesBelow1039_perm :
    (primesBelow 1039).Perm primePrefix1039 := by
  rw [primePrefix1039]
  exact consecutive1033_1039.primesBelow_perm.trans
    (List.Perm.cons 1033 primesBelow1033_perm)

theorem primePrefix1039_gt_one : ∀ q ∈ primePrefix1039, 1 < q := by
  intro q hq
  rw [primePrefix1039] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1033_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1039_1049 : ConsecutivePrimes 1039 1049 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1049. -/
def primePrefix1049 : List Nat :=
  1039 :: primePrefix1039

theorem primesBelow1049_perm :
    (primesBelow 1049).Perm primePrefix1049 := by
  rw [primePrefix1049]
  exact consecutive1039_1049.primesBelow_perm.trans
    (List.Perm.cons 1039 primesBelow1039_perm)

theorem primePrefix1049_gt_one : ∀ q ∈ primePrefix1049, 1 < q := by
  intro q hq
  rw [primePrefix1049] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1039_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1049_1051 : ConsecutivePrimes 1049 1051 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1051. -/
def primePrefix1051 : List Nat :=
  1049 :: primePrefix1049

theorem primesBelow1051_perm :
    (primesBelow 1051).Perm primePrefix1051 := by
  rw [primePrefix1051]
  exact consecutive1049_1051.primesBelow_perm.trans
    (List.Perm.cons 1049 primesBelow1049_perm)

theorem primePrefix1051_gt_one : ∀ q ∈ primePrefix1051, 1 < q := by
  intro q hq
  rw [primePrefix1051] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1049_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1051_1061 : ConsecutivePrimes 1051 1061 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1061. -/
def primePrefix1061 : List Nat :=
  1051 :: primePrefix1051

theorem primesBelow1061_perm :
    (primesBelow 1061).Perm primePrefix1061 := by
  rw [primePrefix1061]
  exact consecutive1051_1061.primesBelow_perm.trans
    (List.Perm.cons 1051 primesBelow1051_perm)

theorem primePrefix1061_gt_one : ∀ q ∈ primePrefix1061, 1 < q := by
  intro q hq
  rw [primePrefix1061] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1051_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1061_1063 : ConsecutivePrimes 1061 1063 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1063. -/
def primePrefix1063 : List Nat :=
  1061 :: primePrefix1061

theorem primesBelow1063_perm :
    (primesBelow 1063).Perm primePrefix1063 := by
  rw [primePrefix1063]
  exact consecutive1061_1063.primesBelow_perm.trans
    (List.Perm.cons 1061 primesBelow1061_perm)

theorem primePrefix1063_gt_one : ∀ q ∈ primePrefix1063, 1 < q := by
  intro q hq
  rw [primePrefix1063] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1061_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1063_1069 : ConsecutivePrimes 1063 1069 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1069. -/
def primePrefix1069 : List Nat :=
  1063 :: primePrefix1063

theorem primesBelow1069_perm :
    (primesBelow 1069).Perm primePrefix1069 := by
  rw [primePrefix1069]
  exact consecutive1063_1069.primesBelow_perm.trans
    (List.Perm.cons 1063 primesBelow1063_perm)

theorem primePrefix1069_gt_one : ∀ q ∈ primePrefix1069, 1 < q := by
  intro q hq
  rw [primePrefix1069] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1063_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive1069_1087 : ConsecutivePrimes 1069 1087 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 1087. -/
def primePrefix1087 : List Nat :=
  1069 :: primePrefix1069

theorem primesBelow1087_perm :
    (primesBelow 1087).Perm primePrefix1087 := by
  rw [primePrefix1087]
  exact consecutive1069_1087.primesBelow_perm.trans
    (List.Perm.cons 1069 primesBelow1069_perm)

theorem primePrefix1087_gt_one : ∀ q ∈ primePrefix1087, 1 < q := by
  intro q hq
  rw [primePrefix1087] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix1069_gt_one q hq

end PrimeFactorUnimodality
