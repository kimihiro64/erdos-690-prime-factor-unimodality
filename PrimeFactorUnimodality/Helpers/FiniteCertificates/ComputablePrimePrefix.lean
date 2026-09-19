import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Chebyshev
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

set_option autoImplicit false

/-!
# A transparent finite primality test

Mathlib's proposition-level primality decider is intentionally opaque.  This
small trial-division Boolean gives finite certificate modules a transparent
computation path, while the theorem below connects it to `Nat.Prime` once and
for all.
-/

namespace PrimeFactorUnimodality

/-- Transparent Boolean primality test based on trial division through
`Nat.minFac`. -/
def isPrimeTrial (n : Nat) : Bool :=
  decide (2 ≤ n) && decide (n.minFac = n)

theorem isPrimeTrial_eq_true_iff (n : Nat) :
    isPrimeTrial n = true ↔ n.Prime := by
  simp only [isPrimeTrial, Bool.and_eq_true, decide_eq_true_eq]
  exact Nat.prime_def_minFac.symm

/-- Ascending list of primes below `p`, produced through the transparent
Boolean primality test. -/
def computablePrimesBelow (p : Nat) : List Nat :=
  (List.range p).filter isPrimeTrial

theorem computablePrimesBelow_perm (p : Nat) :
    (primesBelow p).Perm (computablePrimesBelow p) := by
  apply (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)
    (List.nodup_range.filter isPrimeTrial)).2
  intro q
  simp [isPrimeTrial_eq_true_iff]

theorem primesBelow_eq_computablePrimesBelow (p : Nat) :
    primesBelow p = computablePrimesBelow p := by
  apply List.Perm.eq_of_sortedLE
    (List.Pairwise.sortedLE (primesBelow_pairwise_le p))
    (((List.pairwise_lt_range.filter isPrimeTrial).imp
      (fun h : _ < _ => Nat.le_of_lt h)).sortedLE)
  exact computablePrimesBelow_perm p

theorem computablePrimesBelow_gt_one (p : Nat) :
    ∀ q ∈ computablePrimesBelow p, 1 < q := by
  intro q hq
  have hprime : q.Prime := by
    have hpair : q < p ∧ q.Prime := by
      simpa [computablePrimesBelow, isPrimeTrial_eq_true_iff] using hq
    exact hpair.2
  exact hprime.one_lt

theorem computablePrimesBelow_succ_length (n : Nat) :
    (computablePrimesBelow (n + 1)).length = Nat.primeCounting n := by
  rw [← primesBelow_eq_computablePrimesBelow]
  rw [primesBelow, Finset.length_sort]
  change (Nat.primesBelow (n + 1)).card = Nat.primeCounting n
  rw [Nat.primesBelow_card_eq_primeCounting']
  exact (Nat.primeCounting_eq_primeCounting'_succ n).symm

theorem theta_nat_eq_computablePrimePrefix_log_sum (n : Nat) :
    Chebyshev.theta n =
      (computablePrimesBelow (n + 1)).map Real.log |>.sum := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  rw [← primesBelow_eq_computablePrimesBelow (n + 1)]
  change (∑ p ∈ Nat.primesLE n, Real.log p) =
    (List.map Real.log (primesBelow (n + 1))).sum
  change (∑ p ∈ Nat.primesLE n, Real.log p) =
    (Multiset.map Real.log
      (↑((Nat.primesLE n).sort (fun a b => a ≤ b)) : Multiset Nat)).sum
  rw [Finset.sort_eq]

end PrimeFactorUnimodality
