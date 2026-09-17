import PrimeFactorUnimodality.Proof.SymmetricBounds.Ratio

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

end PrimeFactorUnimodality
