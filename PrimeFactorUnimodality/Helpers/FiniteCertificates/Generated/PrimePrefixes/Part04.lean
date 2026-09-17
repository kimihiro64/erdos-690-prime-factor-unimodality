import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes.Part03


set_option autoImplicit false

/-! Generated consecutive-prime chain and reusable exact prime prefixes. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive257_263 : ConsecutivePrimes 257 263 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 263. -/
def primePrefix263 : List Nat :=
  257 :: primePrefix257

theorem primesBelow263_perm :
    (primesBelow 263).Perm primePrefix263 := by
  rw [primePrefix263]
  exact consecutive257_263.primesBelow_perm.trans
    (List.Perm.cons 257 primesBelow257_perm)

theorem primePrefix263_gt_one : ∀ q ∈ primePrefix263, 1 < q := by
  intro q hq
  rw [primePrefix263] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix257_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive263_269 : ConsecutivePrimes 263 269 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 269. -/
def primePrefix269 : List Nat :=
  263 :: primePrefix263

theorem primesBelow269_perm :
    (primesBelow 269).Perm primePrefix269 := by
  rw [primePrefix269]
  exact consecutive263_269.primesBelow_perm.trans
    (List.Perm.cons 263 primesBelow263_perm)

theorem primePrefix269_gt_one : ∀ q ∈ primePrefix269, 1 < q := by
  intro q hq
  rw [primePrefix269] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix263_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive269_271 : ConsecutivePrimes 269 271 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 271. -/
def primePrefix271 : List Nat :=
  269 :: primePrefix269

theorem primesBelow271_perm :
    (primesBelow 271).Perm primePrefix271 := by
  rw [primePrefix271]
  exact consecutive269_271.primesBelow_perm.trans
    (List.Perm.cons 269 primesBelow269_perm)

theorem primePrefix271_gt_one : ∀ q ∈ primePrefix271, 1 < q := by
  intro q hq
  rw [primePrefix271] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix269_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive271_277 : ConsecutivePrimes 271 277 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 277. -/
def primePrefix277 : List Nat :=
  271 :: primePrefix271

theorem primesBelow277_perm :
    (primesBelow 277).Perm primePrefix277 := by
  rw [primePrefix277]
  exact consecutive271_277.primesBelow_perm.trans
    (List.Perm.cons 271 primesBelow271_perm)

theorem primePrefix277_gt_one : ∀ q ∈ primePrefix277, 1 < q := by
  intro q hq
  rw [primePrefix277] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix271_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive277_281 : ConsecutivePrimes 277 281 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 281. -/
def primePrefix281 : List Nat :=
  277 :: primePrefix277

theorem primesBelow281_perm :
    (primesBelow 281).Perm primePrefix281 := by
  rw [primePrefix281]
  exact consecutive277_281.primesBelow_perm.trans
    (List.Perm.cons 277 primesBelow277_perm)

theorem primePrefix281_gt_one : ∀ q ∈ primePrefix281, 1 < q := by
  intro q hq
  rw [primePrefix281] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix277_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive281_283 : ConsecutivePrimes 281 283 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 283. -/
def primePrefix283 : List Nat :=
  281 :: primePrefix281

theorem primesBelow283_perm :
    (primesBelow 283).Perm primePrefix283 := by
  rw [primePrefix283]
  exact consecutive281_283.primesBelow_perm.trans
    (List.Perm.cons 281 primesBelow281_perm)

theorem primePrefix283_gt_one : ∀ q ∈ primePrefix283, 1 < q := by
  intro q hq
  rw [primePrefix283] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix281_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive283_293 : ConsecutivePrimes 283 293 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 293. -/
def primePrefix293 : List Nat :=
  283 :: primePrefix283

theorem primesBelow293_perm :
    (primesBelow 293).Perm primePrefix293 := by
  rw [primePrefix293]
  exact consecutive283_293.primesBelow_perm.trans
    (List.Perm.cons 283 primesBelow283_perm)

theorem primePrefix293_gt_one : ∀ q ∈ primePrefix293, 1 < q := by
  intro q hq
  rw [primePrefix293] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix283_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive293_307 : ConsecutivePrimes 293 307 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 307. -/
def primePrefix307 : List Nat :=
  293 :: primePrefix293

theorem primesBelow307_perm :
    (primesBelow 307).Perm primePrefix307 := by
  rw [primePrefix307]
  exact consecutive293_307.primesBelow_perm.trans
    (List.Perm.cons 293 primesBelow293_perm)

theorem primePrefix307_gt_one : ∀ q ∈ primePrefix307, 1 < q := by
  intro q hq
  rw [primePrefix307] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix293_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive307_311 : ConsecutivePrimes 307 311 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 311. -/
def primePrefix311 : List Nat :=
  307 :: primePrefix307

theorem primesBelow311_perm :
    (primesBelow 311).Perm primePrefix311 := by
  rw [primePrefix311]
  exact consecutive307_311.primesBelow_perm.trans
    (List.Perm.cons 307 primesBelow307_perm)

theorem primePrefix311_gt_one : ∀ q ∈ primePrefix311, 1 < q := by
  intro q hq
  rw [primePrefix311] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix307_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive311_313 : ConsecutivePrimes 311 313 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 313. -/
def primePrefix313 : List Nat :=
  311 :: primePrefix311

theorem primesBelow313_perm :
    (primesBelow 313).Perm primePrefix313 := by
  rw [primePrefix313]
  exact consecutive311_313.primesBelow_perm.trans
    (List.Perm.cons 311 primesBelow311_perm)

theorem primePrefix313_gt_one : ∀ q ∈ primePrefix313, 1 < q := by
  intro q hq
  rw [primePrefix313] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix311_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive313_317 : ConsecutivePrimes 313 317 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 317. -/
def primePrefix317 : List Nat :=
  313 :: primePrefix313

theorem primesBelow317_perm :
    (primesBelow 317).Perm primePrefix317 := by
  rw [primePrefix317]
  exact consecutive313_317.primesBelow_perm.trans
    (List.Perm.cons 313 primesBelow313_perm)

theorem primePrefix317_gt_one : ∀ q ∈ primePrefix317, 1 < q := by
  intro q hq
  rw [primePrefix317] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix313_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive317_331 : ConsecutivePrimes 317 331 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 331. -/
def primePrefix331 : List Nat :=
  317 :: primePrefix317

theorem primesBelow331_perm :
    (primesBelow 331).Perm primePrefix331 := by
  rw [primePrefix331]
  exact consecutive317_331.primesBelow_perm.trans
    (List.Perm.cons 317 primesBelow317_perm)

theorem primePrefix331_gt_one : ∀ q ∈ primePrefix331, 1 < q := by
  intro q hq
  rw [primePrefix331] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix317_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive331_337 : ConsecutivePrimes 331 337 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 337. -/
def primePrefix337 : List Nat :=
  331 :: primePrefix331

theorem primesBelow337_perm :
    (primesBelow 337).Perm primePrefix337 := by
  rw [primePrefix337]
  exact consecutive331_337.primesBelow_perm.trans
    (List.Perm.cons 331 primesBelow331_perm)

theorem primePrefix337_gt_one : ∀ q ∈ primePrefix337, 1 < q := by
  intro q hq
  rw [primePrefix337] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix331_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive337_347 : ConsecutivePrimes 337 347 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 347. -/
def primePrefix347 : List Nat :=
  337 :: primePrefix337

theorem primesBelow347_perm :
    (primesBelow 347).Perm primePrefix347 := by
  rw [primePrefix347]
  exact consecutive337_347.primesBelow_perm.trans
    (List.Perm.cons 337 primesBelow337_perm)

theorem primePrefix347_gt_one : ∀ q ∈ primePrefix347, 1 < q := by
  intro q hq
  rw [primePrefix347] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix337_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive347_349 : ConsecutivePrimes 347 349 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 349. -/
def primePrefix349 : List Nat :=
  347 :: primePrefix347

theorem primesBelow349_perm :
    (primesBelow 349).Perm primePrefix349 := by
  rw [primePrefix349]
  exact consecutive347_349.primesBelow_perm.trans
    (List.Perm.cons 347 primesBelow347_perm)

theorem primePrefix349_gt_one : ∀ q ∈ primePrefix349, 1 < q := by
  intro q hq
  rw [primePrefix349] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix347_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive349_353 : ConsecutivePrimes 349 353 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 353. -/
def primePrefix353 : List Nat :=
  349 :: primePrefix349

theorem primesBelow353_perm :
    (primesBelow 353).Perm primePrefix353 := by
  rw [primePrefix353]
  exact consecutive349_353.primesBelow_perm.trans
    (List.Perm.cons 349 primesBelow349_perm)

theorem primePrefix353_gt_one : ∀ q ∈ primePrefix353, 1 < q := by
  intro q hq
  rw [primePrefix353] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix349_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive353_359 : ConsecutivePrimes 353 359 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 359. -/
def primePrefix359 : List Nat :=
  353 :: primePrefix353

theorem primesBelow359_perm :
    (primesBelow 359).Perm primePrefix359 := by
  rw [primePrefix359]
  exact consecutive353_359.primesBelow_perm.trans
    (List.Perm.cons 353 primesBelow353_perm)

theorem primePrefix359_gt_one : ∀ q ∈ primePrefix359, 1 < q := by
  intro q hq
  rw [primePrefix359] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix353_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive359_367 : ConsecutivePrimes 359 367 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 367. -/
def primePrefix367 : List Nat :=
  359 :: primePrefix359

theorem primesBelow367_perm :
    (primesBelow 367).Perm primePrefix367 := by
  rw [primePrefix367]
  exact consecutive359_367.primesBelow_perm.trans
    (List.Perm.cons 359 primesBelow359_perm)

theorem primePrefix367_gt_one : ∀ q ∈ primePrefix367, 1 < q := by
  intro q hq
  rw [primePrefix367] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix359_gt_one q hq

end PrimeFactorUnimodality
