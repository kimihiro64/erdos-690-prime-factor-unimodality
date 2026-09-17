import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorUnimodality.Definitions.FiniteDensity

set_option autoImplicit false

/-!
# Exact first-difference threshold

This module proves the algebraic threshold criterion from Wang--Crapis.  It is
stated for an arbitrary list of smaller divisibility moduli; later modules
specialize the list to the primes preceding two consecutive primes.
-/

namespace PrimeFactorUnimodality

/-- Adding one divisibility event updates a positive-index density by the
prime-admission recurrence. -/
theorem finiteDensity_cons_succ (p : Nat) (smallerPrimes : List Nat) (r : Nat) :
    finiteDensity (p :: smallerPrimes) (r + 1) =
      (((p - 1 : Nat) : Rat) / (p : Rat)) * finiteDensity smallerPrimes (r + 1) +
        (1 / (p : Rat)) * finiteDensity smallerPrimes r := by
  rfl

/-- The next prescribed-factor density increases exactly when the preceding
density ratio exceeds one plus the gap.  Here `r + 2` is the one-based factor
position, so the ratio compares the `r`- and `(r + 1)`-event densities. -/
theorem densityStep_iff_symmetricRatio_gap
    (smallerPrimes : List Nat) (r p gap : Nat)
    (hp : 0 < p) (hDensity : 0 < finiteDensity smallerPrimes (r + 1)) :
    prescribedFactorDensity (p :: smallerPrimes) (r + 2) (p + gap) >
          prescribedFactorDensity smallerPrimes (r + 2) p ↔
      densityRatio smallerPrimes (r + 1) > (gap + 1 : Nat) := by
  unfold prescribedFactorDensity densityRatio
  change
    finiteDensity smallerPrimes (r + 1) / (p : Rat) <
          finiteDensity (p :: smallerPrimes) (r + 1) / ((p + gap : Nat) : Rat) ↔
      ((gap + 1 : Nat) : Rat) <
        finiteDensity smallerPrimes r / finiteDensity smallerPrimes (r + 1)
  have hpRat : (0 : Rat) < p := by exact_mod_cast hp
  have hNextRat : (0 : Rat) < p + gap := by positivity
  push_cast
  rw [div_lt_div_iff₀ hpRat hNextRat, lt_div_iff₀ hDensity,
    finiteDensity_cons_succ]
  have hpOne : 1 ≤ p := hp
  rw [Nat.cast_sub hpOne]
  field_simp [ne_of_gt hpRat]
  ring_nf
  constructor <;> intro h <;> linarith

end PrimeFactorUnimodality
