import PrimeFactorUnimodality.Definitions.KthPrimeFactor

set_option autoImplicit false

/-!
# A descent followed by an ascent obstructs unimodality
-/

namespace PrimeFactorUnimodality

theorem not_isUnimodal_of_descent_before_ascent
    (f : Nat → Rat) (i j : Nat) (hij : i < j)
    (hDescent : f (i + 1) < f i) (hAscent : f j < f (j + 1)) :
    ¬ IsUnimodal f := by
  rintro ⟨mode, hIncreasing, hDecreasing⟩
  by_cases himode : i < mode
  · exact (not_lt_of_ge (hIncreasing i himode)) hDescent
  · have hmodei : mode ≤ i := Nat.le_of_not_gt himode
    have hmodej : mode ≤ j := hmodei.trans (Nat.le_of_lt hij)
    exact (not_lt_of_ge (hDecreasing j hmodej)) hAscent

end PrimeFactorUnimodality
