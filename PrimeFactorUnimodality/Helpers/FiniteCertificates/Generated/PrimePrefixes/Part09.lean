import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes.Part08


set_option autoImplicit false

/-! Generated consecutive-prime chain and reusable exact prime prefixes. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive829_839 : ConsecutivePrimes 829 839 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 839. -/
def primePrefix839 : List Nat :=
  829 :: primePrefix829

theorem primesBelow839_perm :
    (primesBelow 839).Perm primePrefix839 := by
  rw [primePrefix839]
  exact consecutive829_839.primesBelow_perm.trans
    (List.Perm.cons 829 primesBelow829_perm)

theorem primePrefix839_gt_one : ∀ q ∈ primePrefix839, 1 < q := by
  intro q hq
  rw [primePrefix839] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix829_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive839_853 : ConsecutivePrimes 839 853 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 853. -/
def primePrefix853 : List Nat :=
  839 :: primePrefix839

theorem primesBelow853_perm :
    (primesBelow 853).Perm primePrefix853 := by
  rw [primePrefix853]
  exact consecutive839_853.primesBelow_perm.trans
    (List.Perm.cons 839 primesBelow839_perm)

theorem primePrefix853_gt_one : ∀ q ∈ primePrefix853, 1 < q := by
  intro q hq
  rw [primePrefix853] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix839_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive853_857 : ConsecutivePrimes 853 857 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 857. -/
def primePrefix857 : List Nat :=
  853 :: primePrefix853

theorem primesBelow857_perm :
    (primesBelow 857).Perm primePrefix857 := by
  rw [primePrefix857]
  exact consecutive853_857.primesBelow_perm.trans
    (List.Perm.cons 853 primesBelow853_perm)

theorem primePrefix857_gt_one : ∀ q ∈ primePrefix857, 1 < q := by
  intro q hq
  rw [primePrefix857] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix853_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive857_859 : ConsecutivePrimes 857 859 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 859. -/
def primePrefix859 : List Nat :=
  857 :: primePrefix857

theorem primesBelow859_perm :
    (primesBelow 859).Perm primePrefix859 := by
  rw [primePrefix859]
  exact consecutive857_859.primesBelow_perm.trans
    (List.Perm.cons 857 primesBelow857_perm)

theorem primePrefix859_gt_one : ∀ q ∈ primePrefix859, 1 < q := by
  intro q hq
  rw [primePrefix859] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix857_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive859_863 : ConsecutivePrimes 859 863 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 863. -/
def primePrefix863 : List Nat :=
  859 :: primePrefix859

theorem primesBelow863_perm :
    (primesBelow 863).Perm primePrefix863 := by
  rw [primePrefix863]
  exact consecutive859_863.primesBelow_perm.trans
    (List.Perm.cons 859 primesBelow859_perm)

theorem primePrefix863_gt_one : ∀ q ∈ primePrefix863, 1 < q := by
  intro q hq
  rw [primePrefix863] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix859_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive863_877 : ConsecutivePrimes 863 877 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 877. -/
def primePrefix877 : List Nat :=
  863 :: primePrefix863

theorem primesBelow877_perm :
    (primesBelow 877).Perm primePrefix877 := by
  rw [primePrefix877]
  exact consecutive863_877.primesBelow_perm.trans
    (List.Perm.cons 863 primesBelow863_perm)

theorem primePrefix877_gt_one : ∀ q ∈ primePrefix877, 1 < q := by
  intro q hq
  rw [primePrefix877] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix863_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive877_881 : ConsecutivePrimes 877 881 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 881. -/
def primePrefix881 : List Nat :=
  877 :: primePrefix877

theorem primesBelow881_perm :
    (primesBelow 881).Perm primePrefix881 := by
  rw [primePrefix881]
  exact consecutive877_881.primesBelow_perm.trans
    (List.Perm.cons 877 primesBelow877_perm)

theorem primePrefix881_gt_one : ∀ q ∈ primePrefix881, 1 < q := by
  intro q hq
  rw [primePrefix881] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix877_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive881_883 : ConsecutivePrimes 881 883 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 883. -/
def primePrefix883 : List Nat :=
  881 :: primePrefix881

theorem primesBelow883_perm :
    (primesBelow 883).Perm primePrefix883 := by
  rw [primePrefix883]
  exact consecutive881_883.primesBelow_perm.trans
    (List.Perm.cons 881 primesBelow881_perm)

theorem primePrefix883_gt_one : ∀ q ∈ primePrefix883, 1 < q := by
  intro q hq
  rw [primePrefix883] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix881_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive883_887 : ConsecutivePrimes 883 887 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 887. -/
def primePrefix887 : List Nat :=
  883 :: primePrefix883

theorem primesBelow887_perm :
    (primesBelow 887).Perm primePrefix887 := by
  rw [primePrefix887]
  exact consecutive883_887.primesBelow_perm.trans
    (List.Perm.cons 883 primesBelow883_perm)

theorem primePrefix887_gt_one : ∀ q ∈ primePrefix887, 1 < q := by
  intro q hq
  rw [primePrefix887] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix883_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive887_907 : ConsecutivePrimes 887 907 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 907. -/
def primePrefix907 : List Nat :=
  887 :: primePrefix887

theorem primesBelow907_perm :
    (primesBelow 907).Perm primePrefix907 := by
  rw [primePrefix907]
  exact consecutive887_907.primesBelow_perm.trans
    (List.Perm.cons 887 primesBelow887_perm)

theorem primePrefix907_gt_one : ∀ q ∈ primePrefix907, 1 < q := by
  intro q hq
  rw [primePrefix907] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix887_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive907_911 : ConsecutivePrimes 907 911 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 911. -/
def primePrefix911 : List Nat :=
  907 :: primePrefix907

theorem primesBelow911_perm :
    (primesBelow 911).Perm primePrefix911 := by
  rw [primePrefix911]
  exact consecutive907_911.primesBelow_perm.trans
    (List.Perm.cons 907 primesBelow907_perm)

theorem primePrefix911_gt_one : ∀ q ∈ primePrefix911, 1 < q := by
  intro q hq
  rw [primePrefix911] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix907_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive911_919 : ConsecutivePrimes 911 919 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 919. -/
def primePrefix919 : List Nat :=
  911 :: primePrefix911

theorem primesBelow919_perm :
    (primesBelow 919).Perm primePrefix919 := by
  rw [primePrefix919]
  exact consecutive911_919.primesBelow_perm.trans
    (List.Perm.cons 911 primesBelow911_perm)

theorem primePrefix919_gt_one : ∀ q ∈ primePrefix919, 1 < q := by
  intro q hq
  rw [primePrefix919] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix911_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive919_929 : ConsecutivePrimes 919 929 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 929. -/
def primePrefix929 : List Nat :=
  919 :: primePrefix919

theorem primesBelow929_perm :
    (primesBelow 929).Perm primePrefix929 := by
  rw [primePrefix929]
  exact consecutive919_929.primesBelow_perm.trans
    (List.Perm.cons 919 primesBelow919_perm)

theorem primePrefix929_gt_one : ∀ q ∈ primePrefix929, 1 < q := by
  intro q hq
  rw [primePrefix929] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix919_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive929_937 : ConsecutivePrimes 929 937 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 937. -/
def primePrefix937 : List Nat :=
  929 :: primePrefix929

theorem primesBelow937_perm :
    (primesBelow 937).Perm primePrefix937 := by
  rw [primePrefix937]
  exact consecutive929_937.primesBelow_perm.trans
    (List.Perm.cons 929 primesBelow929_perm)

theorem primePrefix937_gt_one : ∀ q ∈ primePrefix937, 1 < q := by
  intro q hq
  rw [primePrefix937] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix929_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive937_941 : ConsecutivePrimes 937 941 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 941. -/
def primePrefix941 : List Nat :=
  937 :: primePrefix937

theorem primesBelow941_perm :
    (primesBelow 941).Perm primePrefix941 := by
  rw [primePrefix941]
  exact consecutive937_941.primesBelow_perm.trans
    (List.Perm.cons 937 primesBelow937_perm)

theorem primePrefix941_gt_one : ∀ q ∈ primePrefix941, 1 < q := by
  intro q hq
  rw [primePrefix941] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix937_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive941_947 : ConsecutivePrimes 941 947 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 947. -/
def primePrefix947 : List Nat :=
  941 :: primePrefix941

theorem primesBelow947_perm :
    (primesBelow 947).Perm primePrefix947 := by
  rw [primePrefix947]
  exact consecutive941_947.primesBelow_perm.trans
    (List.Perm.cons 941 primesBelow941_perm)

theorem primePrefix947_gt_one : ∀ q ∈ primePrefix947, 1 < q := by
  intro q hq
  rw [primePrefix947] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix941_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive947_953 : ConsecutivePrimes 947 953 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 953. -/
def primePrefix953 : List Nat :=
  947 :: primePrefix947

theorem primesBelow953_perm :
    (primesBelow 953).Perm primePrefix953 := by
  rw [primePrefix953]
  exact consecutive947_953.primesBelow_perm.trans
    (List.Perm.cons 947 primesBelow947_perm)

theorem primePrefix953_gt_one : ∀ q ∈ primePrefix953, 1 < q := by
  intro q hq
  rw [primePrefix953] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix947_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive953_967 : ConsecutivePrimes 953 967 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 967. -/
def primePrefix967 : List Nat :=
  953 :: primePrefix953

theorem primesBelow967_perm :
    (primesBelow 967).Perm primePrefix967 := by
  rw [primePrefix967]
  exact consecutive953_967.primesBelow_perm.trans
    (List.Perm.cons 953 primesBelow953_perm)

theorem primePrefix967_gt_one : ∀ q ∈ primePrefix967, 1 < q := by
  intro q hq
  rw [primePrefix967] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix953_gt_one q hq

end PrimeFactorUnimodality
