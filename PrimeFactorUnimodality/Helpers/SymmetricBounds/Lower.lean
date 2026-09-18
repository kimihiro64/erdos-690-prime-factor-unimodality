import Mathlib.Tactic.Linarith
import PrimeFactorUnimodality.Helpers.SymmetricBounds.Positivity

set_option autoImplicit false

/-!
# The lower elementary-symmetric ratio estimate

The key polynomial inequality is proved by induction on the finite weight
list.  It holds in every degree, including degrees beyond the list length.
-/

namespace PrimeFactorUnimodality

theorem weightSum_nonneg
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p) :
    0 ≤ weightSum entries := by
  induction entries with
  | nil => simp [weightSum]
  | cons p entries ih =>
      have hp : 1 < p := hentries p (by simp)
      have htail : ∀ q ∈ entries, 1 < q := by
        intro q hq
        exact hentries q (by simp [hq])
      simp only [weightSum, List.map_cons, List.sum_cons]
      exact add_nonneg (le_of_lt (primeWeight_pos p hp)) (ih htail)

theorem weightSum_pos_of_ne_nil
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p)
    (hne : entries ≠ []) :
    0 < weightSum entries := by
  cases entries with
  | nil => exact (hne rfl).elim
  | cons p entries =>
      simp only [weightSum, List.map_cons, List.sum_cons]
      exact add_pos_of_pos_of_nonneg
        (primeWeight_pos p (hentries p (by simp)))
        (weightSum_nonneg entries (fun q hq => hentries q (by simp [hq])))

theorem weightEsymm_one (entries : List Nat) :
    weightEsymm entries 1 = weightSum entries := by
  induction entries with
  | nil =>
      rw [weightEsymm, weightSum]
      simp only [List.map_nil, List.sum_nil]
      have hnil : (↑([] : List Rat) : Multiset Rat) = 0 := rfl
      rw [hnil, Multiset.esymm_of_card_lt (by simp)]
  | cons p entries ih =>
      rw [weightEsymm, weightSum]
      simp only [List.map_cons, List.sum_cons]
      have hcons :
          (↑(primeWeight p :: List.map primeWeight entries) : Multiset Rat) =
            primeWeight p ::ₘ (↑(List.map primeWeight entries) : Multiset Rat) := rfl
      rw [hcons, show 1 = 0 + 1 by rfl, esymm_cons_succ]
      simp only [Multiset.esymm_zero, mul_one]
      change
        (↑(List.map primeWeight entries) : Multiset Rat).esymm 1 =
          (List.map primeWeight entries).sum at ih
      rw [show 0 + 1 = 1 by rfl, ih]
      ac_rfl

/-- The elementary-symmetric double-counting inequality
`r E_r ≤ (Σ w) E_(r-1)`. -/
theorem degree_mul_weightEsymm_le
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p) (r : Nat) :
    (r : Rat) * weightEsymm entries r ≤
      weightSum entries * weightEsymm entries (r - 1) := by
  induction entries generalizing r with
  | nil =>
      cases r with
      | zero => simp [weightEsymm, weightSum]
      | succ r =>
          have hempty : weightEsymm [] (r + 1) = 0 := by
            rw [weightEsymm]
            simp only [List.map_nil]
            have hnil : (↑([] : List Rat) : Multiset Rat) = 0 := rfl
            rw [hnil, Multiset.esymm_of_card_lt (by simp)]
          rw [hempty]
          simp [weightSum]
  | cons p entries ih =>
      have hp : 1 < p := hentries p (by simp)
      have htail : ∀ q ∈ entries, 1 < q := by
        intro q hq
        exact hentries q (by simp [hq])
      cases r with
      | zero =>
          simp only [Nat.cast_zero, zero_mul, Nat.zero_sub, weightEsymm]
          exact mul_nonneg (weightSum_nonneg (p :: entries) hentries)
            (by simp)
      | succ r =>
          cases r with
          | zero =>
              rw [weightEsymm_one]
              simp [weightEsymm]
          | succ r =>
              have ihSucc := ih htail (r + 2)
              have ihBase := ih htail (r + 1)
              have hweight : 0 ≤ primeWeight p := le_of_lt (primeWeight_pos p hp)
              have hprev : 0 ≤ weightEsymm entries r :=
                weightEsymm_nonneg entries htail r
              simp only [weightSum, List.map_cons, List.sum_cons] at ⊢
              simp only [weightEsymm, List.map_cons] at ⊢ ihSucc ihBase hprev
              simp only [weightSum, Nat.cast_add] at ihSucc
              simp only [weightSum, Nat.add_sub_cancel, Nat.cast_add,
                Nat.cast_one] at ihBase
              simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
              have hsub : r + 2 - 1 = r + 1 := by omega
              have htwo : r + 1 + 1 = r + 2 := by omega
              rw [hsub] at ihSucc
              rw [htwo]
              have hcons :
                  (↑(primeWeight p :: List.map primeWeight entries) : Multiset Rat) =
                    primeWeight p ::ₘ
                      (↑(List.map primeWeight entries) : Multiset Rat) := rfl
              simp only [hcons]
              rw [esymm_cons_succ]
              rw [esymm_cons_succ]
              rw [htwo]
              have hscaled :
                  0 ≤ primeWeight p *
                    ((List.map primeWeight entries).sum *
                        (↑(List.map primeWeight entries) : Multiset Rat).esymm r -
                      ((r : Rat) + 1) *
                        (↑(List.map primeWeight entries) : Multiset Rat).esymm (r + 1)) :=
                mul_nonneg hweight (sub_nonneg.mpr ihBase)
              have hsquare :
                  0 ≤ primeWeight p ^ 2 *
                    (↑(List.map primeWeight entries) : Multiset Rat).esymm r :=
                mul_nonneg (sq_nonneg (primeWeight p)) hprev
              norm_num at ihSucc ⊢
              nlinarith

end PrimeFactorUnimodality
