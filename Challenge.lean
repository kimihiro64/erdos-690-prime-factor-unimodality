import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Rat.Defs
import Mathlib.NumberTheory.PrimeCounting

set_option autoImplicit false

namespace PrimeFactorUnimodality

/-- The finite density recursion used in the public statement.  The challenge
file repeats this small definition so its statement surface has no project
imports and can be audited independently. -/
def finiteDensity : List Nat → Nat → Rat
  | [], 0 => 1
  | [], _ + 1 => 0
  | p :: primes, 0 => (((p - 1 : Nat) : Rat) / (p : Rat)) * finiteDensity primes 0
  | p :: primes, r + 1 =>
      (((p - 1 : Nat) : Rat) / (p : Rat)) * finiteDensity primes (r + 1) +
        (1 / (p : Rat)) * finiteDensity primes r

def prescribedFactorDensity (smallerPrimes : List Nat) (k p : Nat) : Rat :=
  finiteDensity smallerPrimes (k - 1) / (p : Rat)

def primesBelow (p : Nat) : List Nat :=
  ((Finset.range p).filter Nat.Prime).sort (fun a b => a ≤ b)

noncomputable section

def primeAt (i : Nat) : Nat := Nat.nth Nat.Prime i

def primeFactorDensity (k i : Nat) : Rat :=
  prescribedFactorDensity (primesBelow (primeAt i)) k (primeAt i)

def IsUnimodal (f : Nat → Rat) : Prop :=
  ∃ mode : Nat,
    (∀ i, i < mode → f i ≤ f (i + 1)) ∧
      (∀ i, mode ≤ i → f (i + 1) ≤ f i)

def CompleteClassification : Prop :=
  ∀ k : Nat, 1 ≤ k → (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3)

end

end PrimeFactorUnimodality

/-!
# All-k Erdős 690 challenge

This is the exact universal statement of the Wang--Crapis classification:
the prime-factor density sequence is unimodal precisely for `k ≤ 3`.
The definitions are repeated here so the challenge remains an auditable,
Mathlib-only statement surface.
-/

theorem PrimeFactorUnimodality.completeClassification :
    PrimeFactorUnimodality.CompleteClassification := by
  sorry
