import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.PrimeFin
import PrimeFactorUnimodality.Definitions.KthPrimeFactor
import PrimeFactorUnimodality.Definitions.NaturalDensity
import PrimeFactorUnimodality.Definitions.SelectionNumerator
import PrimeFactorUnimodality.Mathlib.Data.Nat.CoprimePeriodicCount

set_option autoImplicit false

/-!
# Finite prime-divisibility predicates

These predicates remove the one-point `n ≠ 0` anomaly from the original
prime-factor statement.  Their periodicity is the exact finite input to the
natural-density argument.
-/

open Function

namespace PrimeFactorUnimodality

/-- The number of entries in a finite list which divide `n`. -/
def selectedDivisorCount (entries : List ℕ) (n : ℕ) : ℕ :=
  (entries.filter fun entry => entry ∣ n).length

/-- Divisibility by `p`, together with exactly `r` selected divisors from a
finite list. -/
def HasSelectedDivisors (entries : List ℕ) (r p n : ℕ) : Prop :=
  p ∣ n ∧ selectedDivisorCount entries n = r

theorem hasSelectedDivisors_cons_zero_iff (q : ℕ) (entries : List ℕ) (p n : ℕ) :
    HasSelectedDivisors (q :: entries) 0 p n ↔
      ¬ q ∣ n ∧ HasSelectedDivisors entries 0 p n := by
  by_cases hq : q ∣ n <;>
    simp [HasSelectedDivisors, selectedDivisorCount, hq]

theorem hasSelectedDivisors_cons_succ_iff
    (q : ℕ) (entries : List ℕ) (r p n : ℕ) :
    HasSelectedDivisors (q :: entries) (r + 1) p n ↔
      (q ∣ n ∧ HasSelectedDivisors entries r p n) ∨
        (¬ q ∣ n ∧ HasSelectedDivisors entries (r + 1) p n) := by
  by_cases hq : q ∣ n <;>
    simp [HasSelectedDivisors, selectedDivisorCount, hq]

theorem hasSelectedDivisors_empty_iff (p n : ℕ) :
    HasSelectedDivisors [] 0 p n ↔ p ∣ n := by
  simp [HasSelectedDivisors, selectedDivisorCount]

instance instDecidablePredHasSelectedDivisors (entries : List ℕ) (r p : ℕ) :
    DecidablePred (HasSelectedDivisors entries r p) := fun n => by
  unfold HasSelectedDivisors
  infer_instance

theorem count_hasSelectedDivisors_empty (p : ℕ) (hp : 0 < p) :
    Nat.count (HasSelectedDivisors [] 0 p) p = 1 := by
  rw [Nat.count_eq_card_filter_range]
  have hfilter : (Finset.range p).filter (HasSelectedDivisors [] 0 p) = {0} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hnlt, hnp⟩
      rw [hasSelectedDivisors_empty_iff] at hnp
      exact Nat.eq_zero_of_dvd_of_lt hnp hnlt
    · intro hn
      subst n
      exact ⟨hp, dvd_zero p, rfl⟩
  rw [hfilter]
  simp

instance instDecidablePredIsKthDistinctPrimeFactor (k p : ℕ) :
    DecidablePred (fun n => IsKthDistinctPrimeFactor n k p) := fun n => by
  unfold IsKthDistinctPrimeFactor
  infer_instance

theorem selectedDivisorCount_add_of_dvd (entries : List ℕ) {shift : ℕ}
    (shift_dvd : ∀ entry ∈ entries, entry ∣ shift) (n : ℕ) :
    selectedDivisorCount entries (n + shift) =
      selectedDivisorCount entries n := by
  unfold selectedDivisorCount
  congr 1
  apply List.filter_congr
  intro entry entry_mem
  simp only [(Nat.dvd_add_iff_left (shift_dvd entry entry_mem)).symm]

theorem selectedDivisorCount_add_prod (entries : List ℕ) (n : ℕ) :
    selectedDivisorCount entries (n + entries.prod) =
      selectedDivisorCount entries n :=
  selectedDivisorCount_add_of_dvd entries
    (fun _entry entry_mem => List.dvd_prod entry_mem) n

/-- The selected-divisor predicate has period equal to the product of the
candidate divisor and the finite input list. -/
theorem hasSelectedDivisors_periodic (entries : List ℕ) (r p : ℕ) :
    Periodic (HasSelectedDivisors entries r p) (p * entries.prod) := by
  intro n
  apply propext
  have p_dvd_shift : p ∣ p * entries.prod := dvd_mul_right p entries.prod
  have count_periodic :
      selectedDivisorCount entries (n + p * entries.prod) =
        selectedDivisorCount entries n := by
    apply selectedDivisorCount_add_of_dvd
    intro entry entry_mem
    exact dvd_mul_of_dvd_right (List.dvd_prod entry_mem) p
  unfold HasSelectedDivisors
  rw [count_periodic]
  exact and_congr (Nat.dvd_add_iff_left p_dvd_shift).symm Iff.rfl

def ValidSelectionEntries (p : ℕ) : List ℕ → Prop
  | [] => True
  | q :: entries =>
      0 < q ∧ (p * entries.prod).Coprime q ∧ ValidSelectionEntries p entries

theorem validSelectionEntries_prod_pos {p : ℕ} (hp : 0 < p) :
    ∀ {entries : List ℕ}, ValidSelectionEntries p entries → 0 < p * entries.prod
  | [], _ => by simpa using hp
  | q :: entries, hvalid => by
      rw [List.prod_cons]
      exact Nat.mul_pos hp (Nat.mul_pos hvalid.1
        (Nat.pos_of_mul_pos_left
          (validSelectionEntries_prod_pos hp hvalid.2.2)))

theorem validSelectionEntries_of_primes (p : ℕ) (p_prime : p.Prime) :
    ∀ (entries : List ℕ),
      (∀ q ∈ entries, q.Prime) → p ∉ entries → entries.Nodup →
        ValidSelectionEntries p entries
  | [], _, _, _ => trivial
  | q :: entries, all_prime, p_not_mem, nodup => by
      have q_prime : q.Prime := all_prime q (by simp)
      have p_ne_q : p ≠ q := by
        intro hpq
        apply p_not_mem
        simp [hpq]
      have prod_coprime_q : entries.prod.Coprime q := by
        rw [Nat.coprime_list_prod_left_iff]
        intro a ha
        apply (Nat.coprime_primes (all_prime a (by simp [ha])) q_prime).2
        intro haq
        subst a
        exact (List.nodup_cons.mp nodup).1 ha
      refine ⟨q_prime.pos, ?_, ?_⟩
      · rw [Nat.coprime_mul_iff_left]
        exact ⟨(Nat.coprime_primes p_prime q_prime).2 p_ne_q, prod_coprime_q⟩
      · exact validSelectionEntries_of_primes p p_prime entries
          (fun a ha => all_prime a (by simp [ha]))
          (fun hp_mem => p_not_mem (by simp [hp_mem]))
          (List.nodup_cons.mp nodup).2

theorem validSelectionEntries_primesBelow {p : ℕ} (p_prime : p.Prime) :
    ValidSelectionEntries p (primesBelow p) := by
  apply validSelectionEntries_of_primes p p_prime
  · intro q hq
    exact (by simpa [primesBelow] using hq : q < p ∧ q.Prime).2
  · simp [primesBelow]
  · exact Finset.sort_nodup _ _

theorem count_hasSelectedDivisors_eq_selectionNumerator
    (p : ℕ) (hp : 0 < p) :
    ∀ (entries : List ℕ), ValidSelectionEntries p entries → ∀ r : ℕ,
      Nat.count (HasSelectedDivisors entries r p) (p * entries.prod) =
        selectionNumerator entries r
  | [], _, r => by
      cases r with
      | zero => simpa [selectionNumerator] using count_hasSelectedDivisors_empty p hp
      | succ r =>
          apply Nat.count_of_forall_not
          intro n hn
          simp [HasSelectedDivisors, selectedDivisorCount]
  | q :: entries, hvalid, r => by
      have hperiodPos := validSelectionEntries_prod_pos hp hvalid.2.2
      have hbound : p * (q :: entries).prod = (p * entries.prod) * q := by
        simp only [List.prod_cons]
        ac_rfl
      cases r with
      | zero =>
          calc
            Nat.count (HasSelectedDivisors (q :: entries) 0 p)
                (p * (q :: entries).prod) =
                Nat.count (fun n =>
                  HasSelectedDivisors entries 0 p n ∧ ¬ q ∣ n)
                  ((p * entries.prod) * q) := by
              rw [hbound]
              apply Nat.count_congr_iff
              intro n
              rw [hasSelectedDivisors_cons_zero_iff]
              tauto
            _ = (q - 1) * Nat.count (HasSelectedDivisors entries 0 p)
                  (p * entries.prod) :=
              Nat.count_and_not_dvd_mul hperiodPos hvalid.1
                (hasSelectedDivisors_periodic entries 0 p) hvalid.2.1
            _ = selectionNumerator (q :: entries) 0 := by
              rw [count_hasSelectedDivisors_eq_selectionNumerator p hp entries
                hvalid.2.2 0]
              rfl
      | succ r =>
          let left : ℕ → Prop := fun n =>
            HasSelectedDivisors entries r p n ∧ q ∣ n
          let right : ℕ → Prop := fun n =>
            HasSelectedDivisors entries (r + 1) p n ∧ ¬ q ∣ n
          calc
            Nat.count (HasSelectedDivisors (q :: entries) (r + 1) p)
                (p * (q :: entries).prod) =
                Nat.count (fun n => left n ∨ right n)
                  ((p * entries.prod) * q) := by
              rw [hbound]
              apply Nat.count_congr_iff
              intro n
              simpa [left, right, and_comm] using
                hasSelectedDivisors_cons_succ_iff q entries r p n
            _ = Nat.count left ((p * entries.prod) * q) +
                Nat.count right ((p * entries.prod) * q) := by
              apply Nat.count_or_of_disjoint
              intro n
              rintro ⟨⟨_, hqdvd⟩, ⟨_, hqnotdvd⟩⟩
              exact hqnotdvd hqdvd
            _ = Nat.count (HasSelectedDivisors entries r p) (p * entries.prod) +
                (q - 1) * Nat.count
                  (HasSelectedDivisors entries (r + 1) p) (p * entries.prod) := by
              rw [show Nat.count left ((p * entries.prod) * q) =
                    Nat.count (HasSelectedDivisors entries r p) (p * entries.prod) by
                  exact Nat.count_and_dvd_mul hperiodPos hvalid.1
                    (hasSelectedDivisors_periodic entries r p) hvalid.2.1,
                show Nat.count right ((p * entries.prod) * q) =
                    (q - 1) * Nat.count
                      (HasSelectedDivisors entries (r + 1) p) (p * entries.prod) by
                  exact Nat.count_and_not_dvd_mul hperiodPos hvalid.1
                    (hasSelectedDivisors_periodic entries (r + 1) p) hvalid.2.1]
            _ = selectionNumerator (q :: entries) (r + 1) := by
              rw [count_hasSelectedDivisors_eq_selectionNumerator p hp entries
                  hvalid.2.2 r,
                count_hasSelectedDivisors_eq_selectionNumerator p hp entries
                  hvalid.2.2 (r + 1)]
              simp only [selectionNumerator]
              omega

/-- The exact density of the selected-divisor predicate, expressed as its
finite count over one period. -/
theorem hasNaturalDensity_hasSelectedDivisors (entries : List ℕ) (r p : ℕ)
    (period_pos : 0 < p * entries.prod) :
    HasNaturalDensity (HasSelectedDivisors entries r p)
      ((Nat.count (HasSelectedDivisors entries r p) (p * entries.prod) : ℝ) /
        ((p * entries.prod : ℕ) : ℝ)) :=
  hasNaturalDensity_of_periodic period_pos
    (hasSelectedDivisors_periodic entries r p)

theorem hasNaturalDensity_empty_selected (p : ℕ) (hp : 0 < p) :
    HasNaturalDensity (HasSelectedDivisors [] 0 p) (1 / (p : ℝ)) := by
  have hperiod : 0 < p * ([].prod) := by simpa using hp
  have h := hasNaturalDensity_hasSelectedDivisors [] 0 p hperiod
  simpa [count_hasSelectedDivisors_empty p hp] using h

theorem hasNaturalDensity_empty_selected_eq_prescribed (p : ℕ) (hp : 0 < p) :
    HasNaturalDensity (HasSelectedDivisors [] 0 p)
      (finiteDensity [] 0 / (p : ℝ)) := by
  simpa using hasNaturalDensity_empty_selected p hp

theorem selectedDivisorCount_primesBelow (p n : ℕ) (n_ne_zero : n ≠ 0) :
    selectedDivisorCount (primesBelow p) n =
      (n.primeFactors.filter fun q => q < p).card := by
  let candidates := (Finset.range p).filter Nat.Prime
  change (List.filter (fun entry => decide (entry ∣ n))
      (candidates.sort fun a b => a ≤ b)).length = _
  rw [← List.toFinset_card_of_nodup
    ((Finset.sort_nodup candidates (fun a b => a ≤ b)).filter _)]
  congr 1
  ext q
  simp [candidates, Nat.mem_primeFactors, n_ne_zero, and_left_comm, and_assoc]
  tauto

theorem isKthDistinctPrimeFactor_iff_hasSelectedDivisors
    (n k p : ℕ) (n_ne_zero : n ≠ 0) :
    IsKthDistinctPrimeFactor n k p ↔
      p.Prime ∧ HasSelectedDivisors (primesBelow p) (k - 1) p n := by
  rw [IsKthDistinctPrimeFactor, HasSelectedDivisors,
    selectedDivisorCount_primesBelow p n n_ne_zero]
  tauto

theorem isKthDistinctPrimeFactor_iff_withoutZero
    (n k p : ℕ) :
    IsKthDistinctPrimeFactor n k p ↔
      p.Prime ∧ WithoutZero
        (HasSelectedDivisors (primesBelow p) (k - 1) p) n := by
  constructor
  · intro hypothesis
    have n_ne_zero := hypothesis.2.2.1
    exact ⟨hypothesis.1, n_ne_zero,
      (isKthDistinctPrimeFactor_iff_hasSelectedDivisors n k p n_ne_zero).mp
        hypothesis |>.2⟩
  · rintro ⟨p_prime, n_ne_zero, selected⟩
    exact (isKthDistinctPrimeFactor_iff_hasSelectedDivisors n k p n_ne_zero).mpr
      ⟨p_prime, selected⟩

theorem primesBelow_prod_pos {p : ℕ} : 0 < (primesBelow p).prod := by
  apply List.prod_pos
  intro q q_mem
  have q_prime : q.Prime := by
    exact (by simpa [primesBelow] using q_mem : q < p ∧ q.Prime).2
  exact q_prime.pos

/-- The original k-th-prime-factor predicate has the natural density obtained
by counting the corresponding divisibility pattern over one finite period. -/
theorem hasNaturalDensity_isKthDistinctPrimeFactor (k : ℕ) {p : ℕ}
    (p_prime : p.Prime) :
    HasNaturalDensity (fun n => IsKthDistinctPrimeFactor n k p)
      ((Nat.count (HasSelectedDivisors (primesBelow p) (k - 1) p)
          (p * (primesBelow p).prod) : ℝ) /
        ((p * (primesBelow p).prod : ℕ) : ℝ)) := by
  have period_pos : 0 < p * (primesBelow p).prod :=
    Nat.mul_pos p_prime.pos primesBelow_prod_pos
  have selected_density :=
    (hasNaturalDensity_hasSelectedDivisors (primesBelow p) (k - 1) p period_pos).withoutZero
  exact selected_density.congr fun n => by
    simpa [p_prime] using
      (isKthDistinctPrimeFactor_iff_withoutZero n k p).symm

/-- The periodic count agrees with the exact rational formula used throughout
the classification proof. -/
theorem hasNaturalDensity_isKthDistinctPrimeFactor_eq_prescribed
    (k : ℕ) {p : ℕ} (p_prime : p.Prime) :
    HasNaturalDensity (fun n => IsKthDistinctPrimeFactor n k p)
      (prescribedFactorDensity (primesBelow p) k p : ℝ) := by
  have density := hasNaturalDensity_isKthDistinctPrimeFactor k p_prime
  have entries_gt_one : ∀ q ∈ primesBelow p, 1 < q := by
    intro q hq
    exact ((by simpa [primesBelow] using hq : q < p ∧ q.Prime).2).one_lt
  have count_eq := count_hasSelectedDivisors_eq_selectionNumerator p p_prime.pos
    (primesBelow p) (validSelectionEntries_primesBelow p_prime) (k - 1)
  rw [count_eq] at density
  convert density using 1
  rw [prescribedFactorDensity,
    finiteDensity_eq_selectionNumerator_div (primesBelow p) entries_gt_one]
  simp only [Rat.cast_div, Rat.cast_natCast, selectionDenominator, Nat.cast_mul]
  ring

theorem hasNaturalDensity_primeFactorDensity (k i : ℕ) :
    HasNaturalDensity
      (fun n => IsKthDistinctPrimeFactor n k (primeAt i))
      (primeFactorDensity k i : ℝ) := by
  exact hasNaturalDensity_isKthDistinctPrimeFactor_eq_prescribed k
    (Nat.prime_nth_prime i)

end PrimeFactorUnimodality
