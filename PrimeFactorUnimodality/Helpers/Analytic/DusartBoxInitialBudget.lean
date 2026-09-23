import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxDampedBudget
import PrimeFactorUnimodality.Helpers.Analytic.ZetaZeroFreeBounded

/-! # The box estimate with an unconditional initial low-height gap

The bounded-strip theorem supplies a positive initial gap at any cutoff
above `10^9`. Its use here removes all zero-location and reciprocal-mass
premises from the actual box estimates. The initial constant is deliberately
weak: the remaining scalar inequality at Dusart's fixed cutoff is not
asserted, nor is this a substitute for sharper optimized estimates.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev

/-- The actual finite reciprocal-norm mass has an unconditional explicit initial bound. -/
theorem sum_xi_low_reciprocal_norm_le_initial {a H : ℝ}
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) :
    (∑ p ∈ xiLowHeightIndices H, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      xiLowReciprocalNormBound a H (1 / (56 * Real.log H)) :=
  sum_xi_low_reciprocal_norm_le_explicit ha haH (xi_initial_gap_pos hH)
    (xi_low_re_le_initial_gap hH)

/-- No zero-location premise remains in the actual averaged psi bound. -/
theorem abs_dusartPsiAverageError_le_initialBudget (m : ℕ) {h x a H T B : ℝ}
    (hh : 0 < h) (hx : 1 < x) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hTB : T ≤ B) :
    |dusartPsiAverageError (m + 3) h x| ≤
      dusartBoxDampedErrorBudget m h x a H T B (1 / (56 * Real.log H)) :=
  abs_dusartPsiAverageError_le_dampedBudget m hh hx ha haH hH hHT hTB
    (xi_initial_gap_pos hH) (xi_low_re_le_initial_gap hH)

/-- The initial region yields a completely unconditional pointwise box estimate. -/
theorem abs_psi_sub_le_dusartBoxInitialBudget (m : ℕ) {h x a H T B : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hTB : T ≤ B) :
    |ψ x - x| ≤
      max (dusartBoxDampedErrorBudget m h (x - (m + 3 : ℕ) * h) a H T B
        (1 / (56 * Real.log H)))
        (dusartBoxDampedErrorBudget m h x a H T B (1 / (56 * Real.log H))) +
      (m + 3 : ℕ) * h / 2 :=
  abs_psi_sub_le_dusartBoxDampedBudget m hh hx ha haH hH hHT hTB
    (xi_initial_gap_pos hH) (xi_low_re_le_initial_gap hH)

/-- This route leaves only the scalar budget, not an assumed theorem about low zeros. -/
theorem hasPsiLogFourthError_of_initialBudget {A X H : ℝ} (hH : 10 ^ 9 ≤ H)
    (h : HasDusartDampedScalarBudget A X H (1 / (56 * Real.log H))) :
    HasPsiLogFourthError A X :=
  hasPsiLogFourthError_of_dampedBudget hH (xi_initial_gap_pos hH)
    (xi_low_re_le_initial_gap hH) h

end

end PrimeFactorUnimodality
