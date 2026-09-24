import PrimeFactorUnimodality.Helpers.Arithmetic.SievePrimeProduct

/-! # Exact primorial products, trace composition and rejected incomplete coverage -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open PrimeCert.Sieve SieveProductRow

private theorem sieve30 : IsSieve 30 766 :=
  isSieve_of_sieveK_eq (sqrtN := 6) (by decide +kernel) (by decide) (by decide)

private def rows : List SieveProductRow := [⟨4, 2, 5005⟩, ⟨5, 3, 215441⟩]

example : checkPrimorial 30 766 rows 6469693230 = true := by decide +kernel
example : primorial 30 = 6469693230 :=
  primorial_eq_of_check sieve30 (by decide) (rows := rows) (by decide +kernel)

example {N n bits k : ℕ} (h : IsSieve N bits) (hn : n ≤ N)
    (hk : wheelLength n - 1 ≤ 2 ^ k) : primorial n = sievePrimeProduct k n bits :=
  primorial_eq_sievePrimeProduct h hn hk

example (bits start : ℕ) (left right : List SieveProductRow)
    (hl : checkTrace bits start left = true)
    (hr : checkTrace bits (start + (left.map width).sum) right = true) :
    checkTrace bits start (left ++ right) = true := by
  rw [checkTrace_append, hl, hr]
  rfl

example : checkPrimorial 30 766 [⟨4, 2, 5005⟩] 30030 = false := by decide +kernel
example : checkPrimorial 30 766 rows 6469693231 = false := by decide +kernel
example : (SieveProductRow.mk 5 2 5005).check 766 1 = false := by decide +kernel
example : checkPrimorial 0 766 [] 1 = true := by decide +kernel
example : checkPrimorial 1 766 [] 1 = true := by decide +kernel
example : checkPrimorial 2 766 [] 2 = true := by decide +kernel
example : checkPrimorial 3 766 [] 6 = true := by decide +kernel
example : primorial 0 = 1 :=
  primorial_eq_of_check sieve30 (by decide) (rows := []) (by decide +kernel)
example : primorial 2 = 2 :=
  primorial_eq_of_check sieve30 (by decide) (rows := []) (by decide +kernel)

end PrimeFactorUnimodality.Tests
