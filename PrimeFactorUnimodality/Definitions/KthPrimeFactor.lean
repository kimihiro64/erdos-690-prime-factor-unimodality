import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.PrimeCounting
import PrimeFactorUnimodality.Definitions.FiniteDensity

set_option autoImplicit false

/-!
# The k-th distinct prime factor and its density sequence

Prime positions are one-based in the mathematical problem and prime indices
are zero-based in Lean.  The predicate counts distinct prime divisors below
the candidate prime, so multiplicities do not affect the position.
-/

namespace PrimeFactorUnimodality

/-- The increasing list of all primes strictly below `p`. -/
def primesBelow (p : Nat) : List Nat :=
  ((Finset.range p).filter Nat.Prime).sort (fun a b => a ≤ b)

noncomputable section

/-- The zero-based `i`-th prime. -/
def primeAt (i : Nat) : Nat := Nat.nth Nat.Prime i

/-- The gap following the zero-based `i`-th prime. -/
def primeGap (i : Nat) : Nat := primeAt (i + 1) - primeAt i

/-- `p` is the one-based `k`-th smallest distinct prime divisor of `n`. -/
def IsKthDistinctPrimeFactor (n k p : Nat) : Prop :=
  p.Prime ∧ p ∣ n ∧ n ≠ 0 ∧
    ((n.primeFactors.filter fun q => q < p).card = k - 1)

/-- The exact finite formula for the density at the `i`-th prime. -/
def primeFactorDensity (k i : Nat) : Rat :=
  prescribedFactorDensity (primesBelow (primeAt i)) k (primeAt i)

/-- Discrete unimodality: weak increase through a mode, followed by weak
decrease. -/
def IsUnimodal (f : Nat → Rat) : Prop :=
  ∃ mode : Nat,
    (∀ i, i < mode → f i ≤ f (i + 1)) ∧
      (∀ i, mode ≤ i → f (i + 1) ≤ f i)

/-- The complete classification requested by Erdős Problem 690. -/
def CompleteClassification : Prop :=
  ∀ k : Nat, 1 ≤ k → (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3)

end

end PrimeFactorUnimodality
