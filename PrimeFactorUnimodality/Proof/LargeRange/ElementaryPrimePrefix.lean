import Mathlib.NumberTheory.Chebyshev
import PrimeFactorUnimodality.Proof.LargeRange.TailPrefixBounds

set_option autoImplicit false

/-! # An elementary indexed-prime upper bound

This replaces the explicit Dusart prime-counting input in the uniform tail by
Mathlib's proved Chebyshev lower bound.
-/

namespace PrimeFactorUnimodality

noncomputable section

def elementaryPrimeUpper (r : Nat) : Nat := 4 * tailPrimeUpper r

theorem elementaryPrimeUpper_log_lt {r : Nat} (hr : 38000 ≤ r) :
    Real.log (elementaryPrimeUpper r) <
      (Nat.log 2 r : Real) + 7 / 5 := by
  have tailPos : (0 : Real) < tailPrimeUpper r := by
    exact_mod_cast (show 0 < tailPrimeUpper r by
      simp only [tailPrimeUpper]
      exact Nat.mul_pos (by omega) (Nat.log_pos (by omega) (by omega)))
  rw [elementaryPrimeUpper, Nat.cast_mul, Nat.cast_ofNat,
    Real.log_mul (by norm_num) tailPos.ne', Real.log_four_eq]
  have tailLog := tail_log_upper_lt hr
  nlinarith [Real.log_two_lt_d9]

theorem elementaryPrimeUpper_succ_log_lt {r : Nat} (hr : 38000 ≤ r) :
    Real.log (elementaryPrimeUpper r + 1) <
      (Nat.log 2 r : Real) + 21 / 10 := by
  have upperPos : 1 ≤ elementaryPrimeUpper r := by
    simp only [elementaryPrimeUpper, tailPrimeUpper]
    have logPos : 1 ≤ Nat.log 2 r :=
      Nat.log_pos (by omega) (by omega)
    nlinarith
  have succLe : elementaryPrimeUpper r + 1 ≤ 2 * elementaryPrimeUpper r := by
    omega
  have castSuccPos : (0 : Real) < (elementaryPrimeUpper r + 1 : Nat) := by
    exact_mod_cast (show 0 < elementaryPrimeUpper r + 1 by omega)
  have castSuccLe : ((elementaryPrimeUpper r + 1 : Nat) : Real) ≤
      ((2 * elementaryPrimeUpper r : Nat) : Real) := by
    exact_mod_cast succLe
  have logged := Real.log_le_log castSuccPos castSuccLe
  have upperRealPos : (0 : Real) < elementaryPrimeUpper r := by
    exact_mod_cast (show 0 < elementaryPrimeUpper r by omega)
  rw [Nat.cast_mul, Nat.cast_ofNat,
    Real.log_mul (by norm_num) upperRealPos.ne'] at logged
  have upperLog := elementaryPrimeUpper_log_lt hr
  have logTwo : Real.log 2 < (7 : Real) / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have logged' : Real.log ((elementaryPrimeUpper r : Real) + 1) ≤
      Real.log 2 + Real.log (elementaryPrimeUpper r) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] using logged
  linarith

/-- For `r ≥ 38000`, the zero-based `r`th prime is below
`4 r floor(log₂ r)`. -/
theorem primeAt_le_elementaryPrimeUpper {r : Nat} (hr : 38000 ≤ r) :
    primeAt r ≤ elementaryPrimeUpper r := by
  let L := Nat.log 2 r
  let U := elementaryPrimeUpper r
  have Llarge : (15 : Real) ≤ L := by
    exact_mod_cast (show 15 ≤ Nat.log 2 r by
      apply Nat.le_log_of_pow_le (by omega)
      norm_num
      omega)
  have rLarge : (38000 : Real) ≤ r := by exact_mod_cast hr
  have Ucast : (U : Real) = 4 * r * L := by
    simp only [U, elementaryPrimeUpper, tailPrimeUpper, L]
    push_cast
    ring
  have Ugt : 1 < U := by
    dsimp only [U, elementaryPrimeUpper, tailPrimeUpper]
    have : 1 ≤ Nat.log 2 r := Nat.log_pos (by omega) (by omega)
    nlinarith
  have logUPos : 0 < Real.log U :=
    Real.log_pos (by exact_mod_cast Ugt)
  have logUBound : Real.log U < (L : Real) + 7 / 5 := by
    simpa only [U, L] using elementaryPrimeUpper_log_lt hr
  have logSuccBound : Real.log (U + 1) < (L : Real) + 21 / 10 := by
    simpa only [U, L] using elementaryPrimeUpper_succ_log_lt hr
  have logTwoLower : (69 / 100 : Real) < Real.log 2 :=
    (by norm_num : (69 / 100 : Real) < 0.6931471803).trans
      Real.log_two_gt_d9
  have numerator : ((r + 1 : Nat) : Real) * Real.log U ≤
      (U : Real) * Real.log 2 - Real.log (U + 1) := by
    push_cast
    have rPos : (0 : Real) < r := by positivity
    have LPos : (0 : Real) < L := by positivity
    have logPart : (r + 1 : Real) * Real.log U <
        (r + 1) * ((L : Real) + 7 / 5) :=
      mul_lt_mul_of_pos_left logUBound (by positivity)
    have succPart : Real.log ((U : Real) + 1) < (L : Real) + 21 / 10 :=
      logSuccBound
    have coarse :
        (r + 1 : Real) * ((L : Real) + 7 / 5) +
            ((L : Real) + 21 / 10) < 2 * r * L := by
      have LLeR : (L : Real) ≤ r := by
        exact_mod_cast (show L ≤ r by
          dsimp only [L]
          exact (Nat.log_lt_self 2 (by omega)).le)
      have productNonneg : 0 ≤ (r : Real) * (L - 15) :=
        mul_nonneg rPos.le (sub_nonneg.mpr Llarge)
      nlinarith
    have main : 2 * r * L < (U : Real) * Real.log 2 := by
      rw [Ucast]
      nlinarith [mul_pos rPos LPos]
    linarith
  have comparison : ((r + 1 : Nat) : Real) ≤
      ((U : Real) * Real.log 2 - Real.log (U + 1)) / Real.log U := by
    rw [le_div_iff₀ logUPos]
    exact numerator
  have chebyshev := Chebyshev.pi_ge U
  have countBound : r + 1 ≤ Nat.primeCounting U := by
    exact_mod_cast comparison.trans chebyshev
  apply primeAt_le_of_succ_le_primeCounting'
  simpa only [Nat.primeCounting, Nat.primeCounting'] using countBound

end

end PrimeFactorUnimodality
