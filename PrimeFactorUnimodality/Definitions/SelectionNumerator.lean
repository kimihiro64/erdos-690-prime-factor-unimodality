import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PrimeFactorUnimodality.Definitions.FiniteDensity

set_option autoImplicit false

/-!
# Integral form of the finite density recursion

Clearing the common product of the input primes turns the rational density
recursion into an integer recursion.  Adjacent density ratios therefore reduce
to comparisons of two natural-number coefficients.  This representation is
particularly useful for independently checkable finite certificates.
-/

namespace PrimeFactorUnimodality

/-- Numerator of `finiteDensity entries r` over the common denominator given
by the product of `entries`. -/
def selectionNumerator : List Nat → Nat → Nat
  | [], 0 => 1
  | [], _ + 1 => 0
  | p :: entries, 0 => (p - 1) * selectionNumerator entries 0
  | p :: entries, r + 1 =>
      (p - 1) * selectionNumerator entries (r + 1) +
        selectionNumerator entries r

/-- Common denominator of every finite-density coefficient. -/
def selectionDenominator (entries : List Nat) : Nat := entries.prod

theorem finiteDensity_eq_selectionNumerator_div
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p) (r : Nat) :
    finiteDensity entries r =
      (selectionNumerator entries r : Rat) / selectionDenominator entries := by
  induction entries generalizing r with
  | nil => cases r <;> simp [finiteDensity, selectionNumerator, selectionDenominator]
  | cons p entries ih =>
      have hpNat : 1 < p := hentries p (by simp)
      have hp : (p : Rat) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hpNat))
      have htail : ∀ q ∈ entries, 1 < q := by
        intro q hq
        exact hentries q (by simp [hq])
      cases r with
      | zero =>
          rw [finiteDensity, selectionNumerator, ih htail]
          simp only [selectionDenominator, List.prod_cons, Nat.cast_mul,
            Nat.cast_sub hpNat.le]
          field_simp
      | succ r =>
          rw [finiteDensity, selectionNumerator, ih htail, ih htail]
          simp only [selectionDenominator, List.prod_cons, Nat.cast_add,
            Nat.cast_mul,
            Nat.cast_sub hpNat.le]
          field_simp

theorem selectionDenominator_ne_zero
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p) :
    selectionDenominator entries ≠ 0 := by
  induction entries with
  | nil => simp [selectionDenominator]
  | cons p entries ih =>
      have hp : p ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt (hentries p (by simp)))
      have htail : ∀ q ∈ entries, 1 < q := by
        intro q hq
        exact hentries q (by simp [hq])
      simpa [selectionDenominator, hp] using ih htail

theorem densityRatio_eq_selectionNumerator_ratio
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p) (r : Nat) :
    densityRatio entries r =
      (selectionNumerator entries (r - 1) : Rat) /
        selectionNumerator entries r := by
  rw [densityRatio, finiteDensity_eq_selectionNumerator_div entries hentries,
    finiteDensity_eq_selectionNumerator_div entries hentries]
  exact div_div_div_cancel_right₀
    (by exact_mod_cast selectionDenominator_ne_zero entries hentries) _ _

end PrimeFactorUnimodality
