import Mathlib.Tactic.Linarith
import PrimeFactorUnimodality.Helpers.SymmetricBounds.Lower

set_option autoImplicit false

/-!
# The upper elementary-symmetric ratio estimate

The proof uses induction on a nonincreasing list of positive weights.  Prefix
sums encode the maximal weight of a subset of the relevant cardinality.
-/

namespace PrimeFactorUnimodality

theorem leadingWeightSum_step_nonneg
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p) (n : Nat) :
    0 ≤ leadingWeightSum entries (n + 1) - leadingWeightSum entries n := by
  induction entries generalizing n with
  | nil =>
      cases n <;> simp [leadingWeightSum]
  | cons p entries ih =>
      have hp : 1 < p := hentries p (by simp)
      have htail : ∀ q ∈ entries, 1 < q := by
        intro q hq
        exact hentries q (by simp [hq])
      cases n with
      | zero =>
          simp [leadingWeightSum, le_of_lt (primeWeight_pos p hp)]
      | succ n =>
          simpa [leadingWeightSum] using ih htail n

/-- Prefix weight sums are monotone in the requested prefix length. -/
theorem leadingWeightSum_mono
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p) :
    Monotone (leadingWeightSum entries) := by
  intro m n hmn
  induction hmn with
  | refl => exact le_rfl
  | @step n hmn ih =>
      have hstep := leadingWeightSum_step_nonneg entries hentries n
      linarith

theorem leadingWeightSum_step_le
    (entries : List Nat) (cap : Rat)
    (hcap0 : 0 ≤ cap) (hcap : ∀ p ∈ entries, primeWeight p ≤ cap) (n : Nat) :
    leadingWeightSum entries (n + 1) - leadingWeightSum entries n ≤ cap := by
  induction entries generalizing n with
  | nil =>
      cases n <;> simpa [leadingWeightSum] using hcap0
  | cons p entries ih =>
      cases n with
      | zero =>
          simpa [leadingWeightSum] using hcap p (by simp)
      | succ n =>
          have htail : ∀ q ∈ entries, primeWeight q ≤ cap := by
            intro q hq
            exact hcap q (by simp [hq])
          simpa [leadingWeightSum] using ih htail n

/-- For nonincreasing positive weights, removing the first `r - 1` weights
from the total gives the complementary upper estimate for `E_(r-1) / E_r`. -/
theorem weightSum_sub_leading_mul_weightEsymm_le
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p)
    (hdescending : entries.Pairwise fun p q => primeWeight q ≤ primeWeight p)
    (r : Nat) (hr : 1 ≤ r) :
    (weightSum entries - leadingWeightSum entries (r - 1)) *
        weightEsymm entries (r - 1) ≤
      (r : Rat) * weightEsymm entries r := by
  induction entries generalizing r with
  | nil =>
      cases r with
      | zero => simp at hr
      | succ r =>
          have hempty : weightEsymm [] (r + 1) = 0 := by
            rw [weightEsymm]
            simp only [List.map_nil]
            have hnil : (↑([] : List Rat) : Multiset Rat) = 0 := rfl
            rw [hnil, Multiset.esymm_of_card_lt (by simp)]
          rw [hempty]
          have hleading : leadingWeightSum [] r = 0 := by
            cases r <;> rfl
          simp [weightSum, hleading]
  | cons p entries ih =>
      have hp : 1 < p := hentries p (by simp)
      have htail : ∀ q ∈ entries, 1 < q := by
        intro q hq
        exact hentries q (by simp [hq])
      have hpair := List.pairwise_cons.mp hdescending
      cases r with
      | zero => simp at hr
      | succ r =>
          cases r with
          | zero =>
              simp only [zero_add, tsub_self, Nat.cast_one, one_mul, ge_iff_le,
                leadingWeightSum, weightEsymm, Multiset.esymm_zero, mul_one, sub_zero]
              change weightSum (p :: entries) ≤ weightEsymm (p :: entries) 1
              rw [weightEsymm_one]
          | succ n =>
              have ihHigher := ih htail hpair.2 (n + 2) (by omega)
              have ihLower := ih htail hpair.2 (n + 1) (by omega)
              have hstepNonneg := leadingWeightSum_step_nonneg entries htail n
              have hstepLe := leadingWeightSum_step_le entries (primeWeight p)
                (le_of_lt (primeWeight_pos p hp)) hpair.1 n
              have hweight : 0 ≤ primeWeight p := le_of_lt (primeWeight_pos p hp)
              have hEn : 0 ≤ weightEsymm entries n :=
                weightEsymm_nonneg entries htail n
              have hEn1 : 0 ≤ weightEsymm entries (n + 1) :=
                weightEsymm_nonneg entries htail (n + 1)
              have hscaledLower :
                  0 ≤ primeWeight p *
                    ((n + 1 : Nat) * weightEsymm entries (n + 1) -
                      (weightSum entries - leadingWeightSum entries n) *
                        weightEsymm entries n) := by
                apply mul_nonneg hweight
                exact sub_nonneg.mpr ihLower
              have hscaledStep :
                  0 ≤ (primeWeight p -
                      (leadingWeightSum entries (n + 1) -
                        leadingWeightSum entries n)) *
                    weightEsymm entries (n + 1) := by
                exact mul_nonneg (sub_nonneg.mpr hstepLe) hEn1
              simp only [weightSum, List.map_cons, List.sum_cons,
                leadingWeightSum, Nat.succ_sub_one] at ⊢
              simp only [weightEsymm, List.map_cons] at ⊢ ihHigher ihLower
              simp only [weightSum] at ihHigher ihLower
              simp only [weightSum, weightEsymm] at hscaledLower hscaledStep
              have htwo : n + 1 + 1 = n + 2 := by omega
              have hcons :
                  (↑(primeWeight p :: List.map primeWeight entries) : Multiset Rat) =
                    primeWeight p ::ₘ
                      (↑(List.map primeWeight entries) : Multiset Rat) := rfl
              simp only [hcons]
              rw [esymm_cons_succ, esymm_cons_succ]
              rw [htwo]
              norm_num at ihHigher ihLower ⊢
              nlinarith

end PrimeFactorUnimodality
