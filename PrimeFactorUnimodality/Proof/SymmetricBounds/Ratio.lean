import Mathlib.Tactic.FieldSimp
import PrimeFactorUnimodality.Proof.SymmetricBounds.Positivity

set_option autoImplicit false

/-!
# Cancellation in the finite density ratio

The common Euler-product factor cancels from the ratio controlling adjacent
prime-density differences.  Subsequent estimates can therefore work entirely
with elementary symmetric sums.
-/

namespace PrimeFactorUnimodality

theorem densityRatio_eq_weightEsymm_ratio
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p) (r : Nat) :
    densityRatio entries r = weightEsymm entries (r - 1) / weightEsymm entries r := by
  rw [densityRatio,
    finiteDensity_eq_densityBase_mul_weightEsymm entries hentries (r - 1),
    finiteDensity_eq_densityBase_mul_weightEsymm entries hentries r]
  have hbase : densityBase entries ≠ 0 := ne_of_gt (densityBase_pos entries hentries)
  field_simp

end PrimeFactorUnimodality
