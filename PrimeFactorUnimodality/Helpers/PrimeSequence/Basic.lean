import Mathlib.Tactic.Linarith
import PrimeFactorUnimodality.Definitions.KthPrimeFactor
import PrimeFactorUnimodality.Definitions.SymmetricDensity

set_option autoImplicit false

/-!
# Elementary facts about the indexed prime sequence
-/

namespace PrimeFactorUnimodality

theorem prime_primeAt (i : Nat) : (primeAt i).Prime := by
  exact Nat.prime_nth_prime i

theorem one_lt_primeAt (i : Nat) : 1 < primeAt i :=
  (prime_primeAt i).one_lt

theorem primeAt_strictMono : StrictMono primeAt := by
  exact Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem primeWeight_anti {p q : Nat} (hp : 1 < p) (hpq : p ≤ q) :
    primeWeight q ≤ primeWeight p := by
  have hq : 1 < q := lt_of_lt_of_le hp hpq
  have hpRat : (0 : Rat) < ((p - 1 : Nat) : Rat) := by
    exact_mod_cast Nat.sub_pos_of_lt hp
  have hqRat : (0 : Rat) < ((q - 1 : Nat) : Rat) := by
    exact_mod_cast Nat.sub_pos_of_lt hq
  have hsub : ((p - 1 : Nat) : Rat) ≤ ((q - 1 : Nat) : Rat) := by
    exact_mod_cast Nat.sub_le_sub_right hpq 1
  rw [primeWeight, primeWeight]
  apply (div_le_div_iff₀ hqRat hpRat).2
  simpa using hsub

theorem primesBelow_pairwise_le (p : Nat) :
    (primesBelow p).Pairwise (fun a b => a ≤ b) := by
  exact Finset.pairwise_sort _ _

theorem primesBelow_entries (p q : Nat) (hq : q ∈ primesBelow p) :
    q.Prime ∧ q < p := by
  simpa [primesBelow, and_comm] using hq

theorem primesBelow_gt_one (p : Nat) :
    ∀ q ∈ primesBelow p, 1 < q := by
  intro q hq
  exact (primesBelow_entries p q hq).1.one_lt

theorem primesBelow_primeAt_length (i : Nat) :
    (primesBelow (primeAt i)).length = i := by
  rw [primesBelow, Finset.length_sort]
  change (Nat.primesBelow (primeAt i)).card = i
  rw [Nat.primesBelow_card_eq_primeCounting']
  exact Nat.primeCounting'_nth_eq i

theorem natPrimesBelow_primeAt_succ (i : Nat) :
    Nat.primesBelow (primeAt (i + 1)) =
      insert (primeAt i) (Nat.primesBelow (primeAt i)) := by
  ext q
  simp only [Nat.mem_primesBelow, Finset.mem_insert]
  constructor
  · rintro ⟨hqNext, hqPrime⟩
    have hqLe : q ≤ primeAt i := by
      exact Nat.le_nth_of_lt_nth_succ hqNext hqPrime
    rcases hqLe.eq_or_lt with hEq | hLt
    · exact Or.inl hEq
    · exact Or.inr ⟨hLt, hqPrime⟩
  · rintro (hEq | ⟨hLt, hqPrime⟩)
    · subst q
      exact ⟨primeAt_strictMono (Nat.lt_succ_self i), prime_primeAt i⟩
    · exact ⟨hLt.trans (primeAt_strictMono (Nat.lt_succ_self i)), hqPrime⟩

theorem primesBelow_primeAt_succ_perm (i : Nat) :
    (primesBelow (primeAt (i + 1))).Perm
      (primeAt i :: primesBelow (primeAt i)) := by
  apply Multiset.coe_eq_coe.mp
  change
    (↑((Nat.primesBelow (primeAt (i + 1))).sort (fun a b => a ≤ b)) : Multiset Nat) =
      ↑(primeAt i :: (Nat.primesBelow (primeAt i)).sort (fun a b => a ≤ b))
  simp only [Finset.sort_eq]
  change (Nat.primesBelow (primeAt (i + 1))).val = primeAt i ::ₘ
    (↑((Nat.primesBelow (primeAt i)).sort (fun a b => a ≤ b)) : Multiset Nat)
  rw [Finset.sort_eq]
  rw [natPrimesBelow_primeAt_succ, Finset.insert_val]
  simp [Nat.notMem_primesBelow]

theorem primesBelow_weights_descending (p : Nat) :
    (primesBelow p).Pairwise fun a b => primeWeight b ≤ primeWeight a := by
  have hall := primesBelow_gt_one p
  have hsorted := primesBelow_pairwise_le p
  generalize primesBelow p = entries at hall hsorted ⊢
  induction entries with
  | nil => simp
  | cons a entries ih =>
      rw [List.pairwise_cons] at hsorted ⊢
      constructor
      · intro b hb
        exact primeWeight_anti (hall a (by simp)) (hsorted.1 b hb)
      · apply ih
        · intro q hq
          exact hall q (by simp [hq])
        · exact hsorted.2

end PrimeFactorUnimodality
