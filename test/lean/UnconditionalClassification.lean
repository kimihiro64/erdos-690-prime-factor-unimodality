import PrimeFactorUnimodality.Definitions.DivisibilityPredicate
import Solution

set_option autoImplicit false

/-!
# Exact all-k statement check

Copy the Challenge primitives in an isolated namespace and prove equality of
its recursive density with the implementation before transporting the theorem.
The imported natural-density bridge connects the finite formula to the original
prime-factor predicate. Recursive dependency inspection is run separately.
-/

namespace ChallengeStatementAudit

def finiteDensity : List Nat -> Nat -> Rat
  | [], 0 => 1
  | [], _ + 1 => 0
  | p :: primes, 0 => (((p - 1 : Nat) : Rat) / (p : Rat)) * finiteDensity primes 0
  | p :: primes, r + 1 =>
      (((p - 1 : Nat) : Rat) / (p : Rat)) * finiteDensity primes (r + 1) +
        (1 / (p : Rat)) * finiteDensity primes r

def prescribedFactorDensity (smallerPrimes : List Nat) (k p : Nat) : Rat :=
  finiteDensity smallerPrimes (k - 1) / (p : Rat)

def primesBelow (p : Nat) : List Nat :=
  ((Finset.range p).filter Nat.Prime).sort (fun a b => a <= b)

noncomputable section

def primeAt (i : Nat) : Nat := Nat.nth Nat.Prime i

def primeFactorDensity (k i : Nat) : Rat :=
  prescribedFactorDensity (primesBelow (primeAt i)) k (primeAt i)

def IsUnimodal (f : Nat -> Rat) : Prop :=
  Exists (fun mode : Nat =>
    And (forall i, i < mode -> f i <= f (i + 1))
      (forall i, mode <= i -> f (i + 1) <= f i))

def CompleteClassification : Prop :=
  forall k : Nat, 1 <= k ->
    Iff (IsUnimodal (primeFactorDensity k)) (k <= 3)


theorem finiteDensity_eq (ps : List Nat) (r : Nat) :
    finiteDensity ps r = PrimeFactorUnimodality.finiteDensity ps r := by
  induction ps generalizing r with
  | nil => cases r <;> rfl
  | cons p ps ih =>
    cases r with
    | zero => simp only [finiteDensity, PrimeFactorUnimodality.finiteDensity, ih]
    | succ r => simp only [finiteDensity, PrimeFactorUnimodality.finiteDensity, ih]

theorem primeFactorDensity_eq (k i : Nat) :
    primeFactorDensity k i = PrimeFactorUnimodality.primeFactorDensity k i := by
  change finiteDensity (primesBelow (primeAt i)) (k - 1) / (primeAt i : Rat) =
    PrimeFactorUnimodality.finiteDensity (primesBelow (primeAt i)) (k - 1) /
      (primeAt i : Rat)
  rw [finiteDensity_eq]

theorem exact_challenge_statement : CompleteClassification := by
  intro k hk
  change Iff (PrimeFactorUnimodality.IsUnimodal (primeFactorDensity k)) (k <= 3)
  rw [show primeFactorDensity k = PrimeFactorUnimodality.primeFactorDensity k from
    funext (primeFactorDensity_eq k)]
  exact PrimeFactorUnimodality.completeClassification k hk

end

end ChallengeStatementAudit
