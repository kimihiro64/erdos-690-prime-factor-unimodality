import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Rat.Defs

set_option autoImplicit false

/-!
# All-k Erdős 690 challenge

This is the exact universal statement of the Wang--Crapis classification:
the prime-factor density sequence is unimodal precisely for `k ≤ 3`.
The definitions are repeated here so the challenge remains an auditable,
Mathlib-only statement surface.
-/

namespace PrimeFactorUnimodality

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

theorem PrimeFactorUnimodality.completeClassification :
    PrimeFactorUnimodality.CompleteClassification := by
  sorry
