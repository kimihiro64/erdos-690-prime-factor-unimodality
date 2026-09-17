import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes.Part02


set_option autoImplicit false

/-! Generated consecutive-prime chain and reusable exact prime prefixes. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive157_163 : ConsecutivePrimes 157 163 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 163. -/
def primePrefix163 : List Nat :=
  157 :: primePrefix157

theorem primesBelow163_perm :
    (primesBelow 163).Perm primePrefix163 := by
  rw [primePrefix163]
  exact consecutive157_163.primesBelow_perm.trans
    (List.Perm.cons 157 primesBelow157_perm)

theorem primePrefix163_gt_one : ∀ q ∈ primePrefix163, 1 < q := by
  intro q hq
  rw [primePrefix163] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix157_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive163_167 : ConsecutivePrimes 163 167 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 167. -/
def primePrefix167 : List Nat :=
  163 :: primePrefix163

theorem primesBelow167_perm :
    (primesBelow 167).Perm primePrefix167 := by
  rw [primePrefix167]
  exact consecutive163_167.primesBelow_perm.trans
    (List.Perm.cons 163 primesBelow163_perm)

theorem primePrefix167_gt_one : ∀ q ∈ primePrefix167, 1 < q := by
  intro q hq
  rw [primePrefix167] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix163_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive167_173 : ConsecutivePrimes 167 173 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 173. -/
def primePrefix173 : List Nat :=
  167 :: primePrefix167

theorem primesBelow173_perm :
    (primesBelow 173).Perm primePrefix173 := by
  rw [primePrefix173]
  exact consecutive167_173.primesBelow_perm.trans
    (List.Perm.cons 167 primesBelow167_perm)

theorem primePrefix173_gt_one : ∀ q ∈ primePrefix173, 1 < q := by
  intro q hq
  rw [primePrefix173] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix167_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive173_179 : ConsecutivePrimes 173 179 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 179. -/
def primePrefix179 : List Nat :=
  173 :: primePrefix173

theorem primesBelow179_perm :
    (primesBelow 179).Perm primePrefix179 := by
  rw [primePrefix179]
  exact consecutive173_179.primesBelow_perm.trans
    (List.Perm.cons 173 primesBelow173_perm)

theorem primePrefix179_gt_one : ∀ q ∈ primePrefix179, 1 < q := by
  intro q hq
  rw [primePrefix179] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix173_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive179_181 : ConsecutivePrimes 179 181 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 181. -/
def primePrefix181 : List Nat :=
  179 :: primePrefix179

theorem primesBelow181_perm :
    (primesBelow 181).Perm primePrefix181 := by
  rw [primePrefix181]
  exact consecutive179_181.primesBelow_perm.trans
    (List.Perm.cons 179 primesBelow179_perm)

theorem primePrefix181_gt_one : ∀ q ∈ primePrefix181, 1 < q := by
  intro q hq
  rw [primePrefix181] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix179_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive181_191 : ConsecutivePrimes 181 191 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 191. -/
def primePrefix191 : List Nat :=
  181 :: primePrefix181

theorem primesBelow191_perm :
    (primesBelow 191).Perm primePrefix191 := by
  rw [primePrefix191]
  exact consecutive181_191.primesBelow_perm.trans
    (List.Perm.cons 181 primesBelow181_perm)

theorem primePrefix191_gt_one : ∀ q ∈ primePrefix191, 1 < q := by
  intro q hq
  rw [primePrefix191] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix181_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive191_193 : ConsecutivePrimes 191 193 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 193. -/
def primePrefix193 : List Nat :=
  191 :: primePrefix191

theorem primesBelow193_perm :
    (primesBelow 193).Perm primePrefix193 := by
  rw [primePrefix193]
  exact consecutive191_193.primesBelow_perm.trans
    (List.Perm.cons 191 primesBelow191_perm)

theorem primePrefix193_gt_one : ∀ q ∈ primePrefix193, 1 < q := by
  intro q hq
  rw [primePrefix193] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix191_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive193_197 : ConsecutivePrimes 193 197 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 197. -/
def primePrefix197 : List Nat :=
  193 :: primePrefix193

theorem primesBelow197_perm :
    (primesBelow 197).Perm primePrefix197 := by
  rw [primePrefix197]
  exact consecutive193_197.primesBelow_perm.trans
    (List.Perm.cons 193 primesBelow193_perm)

theorem primePrefix197_gt_one : ∀ q ∈ primePrefix197, 1 < q := by
  intro q hq
  rw [primePrefix197] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix193_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive197_199 : ConsecutivePrimes 197 199 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 199. -/
def primePrefix199 : List Nat :=
  197 :: primePrefix197

theorem primesBelow199_perm :
    (primesBelow 199).Perm primePrefix199 := by
  rw [primePrefix199]
  exact consecutive197_199.primesBelow_perm.trans
    (List.Perm.cons 197 primesBelow197_perm)

theorem primePrefix199_gt_one : ∀ q ∈ primePrefix199, 1 < q := by
  intro q hq
  rw [primePrefix199] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix197_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive199_211 : ConsecutivePrimes 199 211 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 211. -/
def primePrefix211 : List Nat :=
  199 :: primePrefix199

theorem primesBelow211_perm :
    (primesBelow 211).Perm primePrefix211 := by
  rw [primePrefix211]
  exact consecutive199_211.primesBelow_perm.trans
    (List.Perm.cons 199 primesBelow199_perm)

theorem primePrefix211_gt_one : ∀ q ∈ primePrefix211, 1 < q := by
  intro q hq
  rw [primePrefix211] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix199_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive211_223 : ConsecutivePrimes 211 223 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 223. -/
def primePrefix223 : List Nat :=
  211 :: primePrefix211

theorem primesBelow223_perm :
    (primesBelow 223).Perm primePrefix223 := by
  rw [primePrefix223]
  exact consecutive211_223.primesBelow_perm.trans
    (List.Perm.cons 211 primesBelow211_perm)

theorem primePrefix223_gt_one : ∀ q ∈ primePrefix223, 1 < q := by
  intro q hq
  rw [primePrefix223] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix211_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive223_227 : ConsecutivePrimes 223 227 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 227. -/
def primePrefix227 : List Nat :=
  223 :: primePrefix223

theorem primesBelow227_perm :
    (primesBelow 227).Perm primePrefix227 := by
  rw [primePrefix227]
  exact consecutive223_227.primesBelow_perm.trans
    (List.Perm.cons 223 primesBelow223_perm)

theorem primePrefix227_gt_one : ∀ q ∈ primePrefix227, 1 < q := by
  intro q hq
  rw [primePrefix227] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix223_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive227_229 : ConsecutivePrimes 227 229 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 229. -/
def primePrefix229 : List Nat :=
  227 :: primePrefix227

theorem primesBelow229_perm :
    (primesBelow 229).Perm primePrefix229 := by
  rw [primePrefix229]
  exact consecutive227_229.primesBelow_perm.trans
    (List.Perm.cons 227 primesBelow227_perm)

theorem primePrefix229_gt_one : ∀ q ∈ primePrefix229, 1 < q := by
  intro q hq
  rw [primePrefix229] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix227_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive229_233 : ConsecutivePrimes 229 233 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 233. -/
def primePrefix233 : List Nat :=
  229 :: primePrefix229

theorem primesBelow233_perm :
    (primesBelow 233).Perm primePrefix233 := by
  rw [primePrefix233]
  exact consecutive229_233.primesBelow_perm.trans
    (List.Perm.cons 229 primesBelow229_perm)

theorem primePrefix233_gt_one : ∀ q ∈ primePrefix233, 1 < q := by
  intro q hq
  rw [primePrefix233] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix229_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive233_239 : ConsecutivePrimes 233 239 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 239. -/
def primePrefix239 : List Nat :=
  233 :: primePrefix233

theorem primesBelow239_perm :
    (primesBelow 239).Perm primePrefix239 := by
  rw [primePrefix239]
  exact consecutive233_239.primesBelow_perm.trans
    (List.Perm.cons 233 primesBelow233_perm)

theorem primePrefix239_gt_one : ∀ q ∈ primePrefix239, 1 < q := by
  intro q hq
  rw [primePrefix239] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix233_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive239_241 : ConsecutivePrimes 239 241 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 241. -/
def primePrefix241 : List Nat :=
  239 :: primePrefix239

theorem primesBelow241_perm :
    (primesBelow 241).Perm primePrefix241 := by
  rw [primePrefix241]
  exact consecutive239_241.primesBelow_perm.trans
    (List.Perm.cons 239 primesBelow239_perm)

theorem primePrefix241_gt_one : ∀ q ∈ primePrefix241, 1 < q := by
  intro q hq
  rw [primePrefix241] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix239_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive241_251 : ConsecutivePrimes 241 251 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 251. -/
def primePrefix251 : List Nat :=
  241 :: primePrefix241

theorem primesBelow251_perm :
    (primesBelow 251).Perm primePrefix251 := by
  rw [primePrefix251]
  exact consecutive241_251.primesBelow_perm.trans
    (List.Perm.cons 241 primesBelow241_perm)

theorem primePrefix251_gt_one : ∀ q ∈ primePrefix251, 1 < q := by
  intro q hq
  rw [primePrefix251] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix241_gt_one q hq

set_option maxRecDepth 10000 in
set_option linter.unnecessarySeqFocus false in
private theorem consecutive251_257 : ConsecutivePrimes 251 257 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro m hmLeft hmRight
  interval_cases m <;> decide


/-- Generated reverse-ordered list of all primes below 257. -/
def primePrefix257 : List Nat :=
  251 :: primePrefix251

theorem primesBelow257_perm :
    (primesBelow 257).Perm primePrefix257 := by
  rw [primePrefix257]
  exact consecutive251_257.primesBelow_perm.trans
    (List.Perm.cons 251 primesBelow251_perm)

theorem primePrefix257_gt_one : ∀ q ∈ primePrefix257, 1 < q := by
  intro q hq
  rw [primePrefix257] at hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · norm_num
  · exact primePrefix251_gt_one q hq

end PrimeFactorUnimodality
