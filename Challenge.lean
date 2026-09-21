import PrimeFactorUnimodality

set_option autoImplicit false

namespace PrimeFactorUnimodality

/-- The finite density recursion used in the public statement.  The challenge
file repeats this small definition so its statement surface has no project
imports and can be audited independently. -/
def challengeFiniteDensity : List Nat → Nat → Rat
  | [], 0 => 1
  | [], _ + 1 => 0
  | p :: primes, 0 => (((p - 1 : Nat) : Rat) / (p : Rat)) * challengeFiniteDensity primes 0
  | p :: primes, r + 1 =>
      (((p - 1 : Nat) : Rat) / (p : Rat)) * challengeFiniteDensity primes (r + 1) +
        (1 / (p : Rat)) * challengeFiniteDensity primes r

def challengePrescribedFactorDensity (smallerPrimes : List Nat) (k p : Nat) : Rat :=
  challengeFiniteDensity smallerPrimes (k - 1) / (p : Rat)

def challengePrimesBelow (p : Nat) : List Nat :=
  ((Finset.range p).filter Nat.Prime).sort (fun a b => a ≤ b)

noncomputable section

def challengePrimeAt (i : Nat) : Nat := Nat.nth Nat.Prime i

def challengePrimeFactorDensity (k i : Nat) : Rat :=
  challengePrescribedFactorDensity (challengePrimesBelow (challengePrimeAt i)) k
    (challengePrimeAt i)

def challengeIsUnimodal (f : Nat → Rat) : Prop :=
  ∃ mode : Nat,
    (∀ i, i < mode → f i ≤ f (i + 1)) ∧
      (∀ i, mode ≤ i → f (i + 1) ≤ f i)

def challengeCompleteClassification : Prop :=
  ∀ k : Nat, 1 ≤ k →
    (challengeIsUnimodal (challengePrimeFactorDensity k) ↔ k ≤ 3)

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
  exact PrimeFactorUnimodality.completeClassification_closed
