import Mathlib.Data.Rat.Defs

set_option autoImplicit false

/-!
# Fourth prime-factor density witness

The definitions below state Cambie's finite recurrence directly over Mathlib
primitives. The theorem records the first strict valley in the `k = 4`
density sequence.
-/

namespace PrimeFactorUnimodality

/-- Finite density of exactly `r` selected divisibility events. -/
def finiteDensity : List Nat → Nat → Rat
  | [], 0 => 1
  | [], _ + 1 => 0
  | p :: primes, 0 => (((p - 1 : Nat) : Rat) / (p : Rat)) * finiteDensity primes 0
  | p :: primes, r + 1 =>
      (((p - 1 : Nat) : Rat) / (p : Rat)) * finiteDensity primes (r + 1) +
        (1 / (p : Rat)) * finiteDensity primes r

/-- Finite density formula for `p` in one-based prime-factor position `k`. -/
def prescribedFactorDensity (smallerPrimes : List Nat) (k p : Nat) : Rat :=
  finiteDensity smallerPrimes (k - 1) / (p : Rat)

/-- The primes strictly below 13. -/
def primesBefore13 : List Nat := [2, 3, 5, 7, 11]

/-- The primes strictly below 17. -/
def primesBefore17 : List Nat := [2, 3, 5, 7, 11, 13]

/-- The primes strictly below 19. -/
def primesBefore19 : List Nat := [2, 3, 5, 7, 11, 13, 17]

end PrimeFactorUnimodality

theorem PrimeFactorUnimodality.fourthDensityStrictValley :
    PrimeFactorUnimodality.prescribedFactorDensity
          PrimeFactorUnimodality.primesBefore17 4 17 <
        PrimeFactorUnimodality.prescribedFactorDensity
          PrimeFactorUnimodality.primesBefore13 4 13 ∧
      PrimeFactorUnimodality.prescribedFactorDensity
          PrimeFactorUnimodality.primesBefore17 4 17 <
        PrimeFactorUnimodality.prescribedFactorDensity
          PrimeFactorUnimodality.primesBefore19 4 19 := by
  sorry
