import Mathlib.Data.Rat.Defs

set_option autoImplicit false

/-!
# Finite prime-divisibility densities

This module defines the exact rational recursion in Claim 6 of Cambie's
*The k-th prime factor of an integer*. For a finite list of primes, the value
`finiteDensity primes r` is the finite Euler-product density of integers
divisible by exactly `r` members of that list.

The definition is meaningful for arbitrary positive natural entries; primality
is needed only when the value is connected to a density of integers.
-/

namespace PrimeFactorUnimodality

/-- The exact finite density of selecting precisely `r` divisibility events
with probabilities `1 / p`, for the entries `p` in `primes`. -/
def finiteDensity : List Nat → Nat → Rat
  | [], 0 => 1
  | [], _ + 1 => 0
  | p :: primes, 0 => (((p - 1 : Nat) : Rat) / (p : Rat)) * finiteDensity primes 0
  | p :: primes, r + 1 =>
      (((p - 1 : Nat) : Rat) / (p : Rat)) * finiteDensity primes (r + 1) +
        (1 / (p : Rat)) * finiteDensity primes r

/-- The finite formula for the density that the `k`-th smallest selected prime
is `p`, given the ordered list of smaller primes. -/
def prescribedFactorDensity (smallerPrimes : List Nat) (k p : Nat) : Rat :=
  finiteDensity smallerPrimes (k - 1) / (p : Rat)

/-- The ratio controlling the sign of the next prime-density difference. The
source uses this only when `r` is positive and the denominator is positive. -/
def densityRatio (smallerPrimes : List Nat) (r : Nat) : Rat :=
  finiteDensity smallerPrimes (r - 1) / finiteDensity smallerPrimes r

/-- The primes strictly below 13. -/
def primesBefore13 : List Nat := [2, 3, 5, 7, 11]

/-- The primes strictly below 17. -/
def primesBefore17 : List Nat := [2, 3, 5, 7, 11, 13]

/-- The primes strictly below 19. -/
def primesBefore19 : List Nat := [2, 3, 5, 7, 11, 13, 17]

end PrimeFactorUnimodality
