import PrimeFactorUnimodality.Definitions.SymmetricDensity

set_option autoImplicit false

/-!
# Positivity for finite densities and symmetric sums

These lemmas discharge the denominator side conditions needed by all later
density-ratio inequalities.
-/

namespace PrimeFactorUnimodality

theorem primeWeight_pos (p : Nat) (hp : 1 < p) : 0 < primeWeight p := by
  rw [primeWeight, one_div_pos]
  exact_mod_cast Nat.sub_pos_of_lt hp

theorem selectionFactor_pos (p : Nat) (hp : 1 < p) :
    0 < ((p - 1 : Nat) : Rat) / (p : Rat) := by
  apply div_pos
  · exact_mod_cast Nat.sub_pos_of_lt hp
  · exact_mod_cast Nat.zero_lt_of_lt hp

theorem densityBase_pos (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p) :
    0 < densityBase entries := by
  induction entries with
  | nil => simp [densityBase]
  | cons p entries ih =>
      rw [densityBase]
      simp only [List.map_cons, List.prod_cons]
      apply mul_pos (selectionFactor_pos p (hentries p (by simp)))
      apply ih
      intro q hq
      exact hentries q (by simp [hq])

theorem weightEsymm_nonneg
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p) (r : Nat) :
    0 ≤ weightEsymm entries r := by
  induction entries generalizing r with
  | nil =>
      cases r with
      | zero => simp [weightEsymm]
      | succ r =>
          rw [weightEsymm]
          simp only [List.map_nil]
          have hnil : (↑([] : List Rat) : Multiset Rat) = 0 := rfl
          rw [hnil, Multiset.esymm_of_card_lt (by simp)]
  | cons p entries ih =>
      have hp : 1 < p := hentries p (by simp)
      have htail : ∀ q ∈ entries, 1 < q := by
        intro q hq
        exact hentries q (by simp [hq])
      cases r with
      | zero => simp [weightEsymm]
      | succ r =>
          rw [weightEsymm]
          simp only [List.map_cons]
          have hcons :
              (↑(primeWeight p :: List.map primeWeight entries) : Multiset Rat) =
                primeWeight p ::ₘ (↑(List.map primeWeight entries) : Multiset Rat) := rfl
          rw [hcons, esymm_cons_succ]
          exact add_nonneg (ih htail (r + 1))
            (mul_nonneg (le_of_lt (primeWeight_pos p hp)) (ih htail r))

theorem weightEsymm_pos
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p)
    (r : Nat) (hr : r ≤ entries.length) :
    0 < weightEsymm entries r := by
  induction entries generalizing r with
  | nil =>
      have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
      subst r
      simp [weightEsymm]
  | cons p entries ih =>
      have hp : 1 < p := hentries p (by simp)
      have htail : ∀ q ∈ entries, 1 < q := by
        intro q hq
        exact hentries q (by simp [hq])
      cases r with
      | zero => simp [weightEsymm]
      | succ r =>
          have hrTail : r ≤ entries.length := Nat.succ_le_succ_iff.mp hr
          rw [weightEsymm]
          simp only [List.map_cons]
          have hcons :
              (↑(primeWeight p :: List.map primeWeight entries) : Multiset Rat) =
                primeWeight p ::ₘ (↑(List.map primeWeight entries) : Multiset Rat) := rfl
          rw [hcons, esymm_cons_succ]
          exact add_pos_of_nonneg_of_pos
            (weightEsymm_nonneg entries htail (r + 1))
            (mul_pos (primeWeight_pos p hp) (ih htail r hrTail))

theorem finiteDensity_pos
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p)
    (r : Nat) (hr : r ≤ entries.length) :
    0 < finiteDensity entries r := by
  rw [finiteDensity_eq_densityBase_mul_weightEsymm entries hentries r]
  exact mul_pos (densityBase_pos entries hentries)
    (weightEsymm_pos entries hentries r hr)

end PrimeFactorUnimodality
