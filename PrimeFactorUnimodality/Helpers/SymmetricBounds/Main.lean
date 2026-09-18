import PrimeFactorUnimodality.Helpers.SymmetricBounds.Lower
import PrimeFactorUnimodality.Helpers.SymmetricBounds.Ratio
import PrimeFactorUnimodality.Helpers.SymmetricBounds.Upper

set_option autoImplicit false

/-!
# Symmetric bounds interface

This is the public entry point for the elementary-symmetric analysis.  The
exact upper and lower estimates will be added here after their combinatorial
double-counting lemma; the representation, cancellation, and all required
positivity facts are already unconditional for finite lists.
-/

namespace PrimeFactorUnimodality

theorem densityRatio_pos
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p)
    (r : Nat) (hr : r ≤ entries.length) :
    0 < densityRatio entries r := by
  rw [densityRatio_eq_weightEsymm_ratio entries hentries r]
  apply div_pos
  · exact weightEsymm_pos entries hentries (r - 1)
      ((Nat.sub_le r 1).trans hr)
  · exact weightEsymm_pos entries hentries r hr

/-- The universal lower estimate for the symmetric density ratio. -/
theorem degree_div_weightSum_le_densityRatio
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p)
    (r : Nat) (hr : r ≤ entries.length) (hSum : 0 < weightSum entries) :
    (r : Rat) / weightSum entries ≤ densityRatio entries r := by
  rw [densityRatio_eq_weightEsymm_ratio entries hentries r]
  apply (div_le_div_iff₀ hSum (weightEsymm_pos entries hentries r hr)).2
  simpa [mul_comm] using degree_mul_weightEsymm_le entries hentries r

/-- The universal upper estimate for a nonincreasing finite weight list. -/
theorem densityRatio_le_degree_div_weightSum_sub_leading
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p)
    (hdescending : entries.Pairwise fun p q => primeWeight q ≤ primeWeight p)
    (r : Nat) (hrPos : 1 ≤ r) (hr : r ≤ entries.length)
    (hComplement : 0 < weightSum entries - leadingWeightSum entries (r - 1)) :
    densityRatio entries r ≤
      (r : Rat) / (weightSum entries - leadingWeightSum entries (r - 1)) := by
  rw [densityRatio_eq_weightEsymm_ratio entries hentries r]
  apply (div_le_div_iff₀ (weightEsymm_pos entries hentries r hr) hComplement).2
  simpa [mul_comm] using
      weightSum_sub_leading_mul_weightEsymm_le entries hentries hdescending r hrPos

/-- A multiplication-only interface to the upper ratio estimate.  This is
convenient for generated rational certificates because it avoids division in
the final numeric side condition. -/
theorem densityRatio_lt_of_degree_lt_bound_mul_complement
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p)
    (hdescending : entries.Pairwise fun p q => primeWeight q ≤ primeWeight p)
    (r : Nat) (hrPos : 1 ≤ r) (hr : r ≤ entries.length) (bound : Rat)
    (hComplement : 0 < weightSum entries - leadingWeightSum entries (r - 1))
    (hNumeric :
      (r : Rat) < bound *
        (weightSum entries - leadingWeightSum entries (r - 1))) :
    densityRatio entries r < bound := by
  exact (densityRatio_le_degree_div_weightSum_sub_leading entries hentries
    hdescending r hrPos hr hComplement).trans_lt
      ((div_lt_iff₀ hComplement).2 hNumeric)

/-- A multiplication-only interface to the lower ratio estimate. -/
theorem bound_lt_densityRatio_of_bound_mul_weightSum_lt_degree
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p)
    (r : Nat) (hr : r ≤ entries.length) (bound : Rat)
    (hSum : 0 < weightSum entries)
    (hNumeric : bound * weightSum entries < (r : Rat)) :
    bound < densityRatio entries r := by
  exact ((lt_div_iff₀ hSum).2 hNumeric).trans_le
    (degree_div_weightSum_le_densityRatio entries hentries r hr hSum)

end PrimeFactorUnimodality
