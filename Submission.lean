import FtpEvalBench.E690
import Submission.Internal.PrimeFactorUnimodality.Definitions.DivisibilityPredicate
import Submission.Internal.PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive
import Submission.Internal.Solution

set_option autoImplicit false
set_option maxRecDepth 4096

/-! The full classification transported to MathDB's natural-density target. -/

namespace Submission

open Filter
open scoped Topology
open Internal.PrimeFactorUnimodality

theorem ncard_Iio_nat (n : Nat) : (Set.Iio n).ncard = n := by
  have h : Set.Iio n = ((Finset.range n : Finset Nat) : Set Nat) := by
    ext x
    simp
  rw [h, Set.ncard_coe_finset, Finset.card_range]

theorem naturalDensity_toSet {predicate : Nat -> Prop}
    [DecidablePred predicate] {density : Real}
    (h : HasNaturalDensity predicate density) :
    Set.HasDensity {n | predicate n} density := by
  have counts (n : Nat) :
      (Inter.inter {x : Nat | predicate x} (Set.Iio n)).ncard =
        Nat.count predicate n := by
    rw [Nat.count_eq_card_filter_range]
    have hset : Inter.inter {x : Nat | predicate x} (Set.Iio n) =
        (((Finset.range n).filter predicate : Finset Nat) : Set Nat) := by
      ext x
      change Iff (And (predicate x) (x < n))
        (Membership.mem ((Finset.range n).filter predicate) x)
      simp only [Finset.mem_filter, Finset.mem_range, and_comm]
    rw [hset, Set.ncard_coe_finset]
  have partial_value (n : Nat) :
      Set.partialDensity {x | predicate x} Set.univ n =
        (Nat.count predicate n : Real) / (n : Real) := by
    unfold Set.partialDensity
    simp only [Set.inter_univ, Set.univ_inter]
    rw [counts n, ncard_Iio_nat]
  unfold HasNaturalDensity at h
  unfold Set.HasDensity
  convert h using 1
  funext n
  exact partial_value n

theorem indexed_density (k i : Nat) :
    (Problem.kthPrimeFactorSet k (primeAt i)).HasDensity
      (primeFactorDensity k i : Real) := by
  classical
  apply naturalDensity_toSet
    ((hasNaturalDensity_primeFactorDensity k i).congr ?_)
  intro n
  simp [IsKthDistinctPrimeFactor,
    Nat.mem_primeFactors, prime_primeAt, Nat.pos_iff_ne_zero, and_assoc,
    and_left_comm, and_comm]

theorem density_values {k : Nat} {d : Nat -> Real}
    (hd : forall p : Nat, p.Prime ->
      (Problem.kthPrimeFactorSet k p).HasDensity (d p)) (i : Nat) :
    d (primeAt i) = (primeFactorDensity k i : Real) := by
  exact tendsto_nhds_unique (hd (primeAt i) (prime_primeAt i))
    (indexed_density k i)

theorem unimodality_equivalence {k : Nat} {d : Nat -> Real}
    (hd : forall p : Nat, p.Prime ->
      (Problem.kthPrimeFactorSet k p).HasDensity (d p)) :
    Iff (Problem.IsUnimodalOnPrimes d) (IsUnimodal (primeFactorDensity k)) := by
  constructor
  next =>
    intro h
    let m := h.choose
    have hm := h.choose_spec
    let j := Nat.primeCounting' m
    have hj : primeAt j = m := primeAt_primeCounting' m hm.1
    refine Exists.intro j (And.intro ?_ ?_)
    next =>
      intro i hi
      have bound : primeAt (i + 1) <= m := by
        rw [<- hj]
        exact primeAt_strictMono.monotone (by omega)
      have step := hm.2.1 (primeAt i) (primeAt (i + 1))
        (prime_primeAt i) (prime_primeAt (i + 1))
        (primeAt_strictMono.monotone (by omega)) bound
      rw [density_values hd i, density_values hd (i + 1)] at step
      exact_mod_cast step
    next =>
      intro i hi
      have bound : m <= primeAt i := by
        rw [<- hj]
        exact primeAt_strictMono.monotone hi
      have step := hm.2.2 (primeAt i) (primeAt (i + 1))
        (prime_primeAt i) (prime_primeAt (i + 1)) bound
        (primeAt_strictMono.monotone (by omega))
      rw [density_values hd i, density_values hd (i + 1)] at step
      exact_mod_cast step
  next =>
    intro h
    let j := h.choose
    have hj := h.choose_spec
    have up : forall a b : Nat, a <= b -> b <= j ->
        primeFactorDensity k a <= primeFactorDensity k b := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ b hab ih =>
          intro hbj
          exact le_trans (ih (by omega)) (hj.1 b (by omega))
    have down : forall a b : Nat, a <= b -> j <= a ->
        primeFactorDensity k b <= primeFactorDensity k a := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ b hab ih =>
          intro hja
          exact le_trans (hj.2 b (by omega)) (ih hja)
    refine Exists.intro (primeAt j) (And.intro (prime_primeAt j) (And.intro ?_ ?_))
    next =>
      intro p q hp hq hpq hqj
      have hp' := primeAt_primeCounting' p hp
      have hq' := primeAt_primeCounting' q hq
      have indices : Nat.primeCounting' p <= Nat.primeCounting' q :=
        primeAt_strictMono.le_iff_le.mp (by simpa [hp', hq'] using hpq)
      have bound : Nat.primeCounting' q <= j :=
        primeAt_strictMono.le_iff_le.mp (by simpa [hq'] using hqj)
      have step := up _ _ indices bound
      have value_p := density_values hd (Nat.primeCounting' p)
      have value_q := density_values hd (Nat.primeCounting' q)
      rw [hp'] at value_p
      rw [hq'] at value_q
      rw [value_p, value_q]
      exact_mod_cast step
    next =>
      intro p q hp hq hjp hpq
      have hp' := primeAt_primeCounting' p hp
      have hq' := primeAt_primeCounting' q hq
      have indices : Nat.primeCounting' p <= Nat.primeCounting' q :=
        primeAt_strictMono.le_iff_le.mp (by simpa [hp', hq'] using hpq)
      have bound : j <= Nat.primeCounting' p :=
        primeAt_strictMono.le_iff_le.mp (by simpa [hp'] using hjp)
      have step := down _ _ indices bound
      have value_p := density_values hd (Nat.primeCounting' p)
      have value_q := density_values hd (Nat.primeCounting' q)
      rw [hp'] at value_p
      rw [hq'] at value_q
      rw [value_p, value_q]
      exact_mod_cast step

theorem complete_classification : Problem.CompleteClassification := by
  intro k hk d hd
  exact (unimodality_equivalence hd).trans (completeClassification k hk)

def answer : Prop := True

theorem solution : Problem.Target answer := by
  constructor
  next => intro _; exact complete_classification
  next => intro _; trivial

end Submission
