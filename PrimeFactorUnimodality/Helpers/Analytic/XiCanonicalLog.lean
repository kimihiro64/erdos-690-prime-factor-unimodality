import Mathlib.Analysis.SpecialFunctions.Log.Summable
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiHadamardConstant

/-! # Absolute logarithms of the actual xi canonical product

The existing PNT Weierstrass-factor bound and finite divisor sets give
summable deviations from one. Mathlib then supplies summable logarithmic
moduli and the exact log of the full product. No sequence enumeration or
critical-line hypothesis is needed.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter

/-- The actual genus-one factors differ from one by an absolutely summable family. -/
theorem summable_norm_xi_weierstrass_sub_one (z : ℂ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      ‖weierstrassFactor 1 (z / riemannXiDivisorZeroValue p) - 1‖) := by
  have hfin : {p : RiemannXiDivisorZeroIndex |
      ‖riemannXiDivisorZeroValue p‖ ≤ 2 * ‖z‖}.Finite :=
    Hadamard.divisorZeroIndex₀_norm_le_finite
      (f := riemannXi) (U := Set.univ) (B := 2 * ‖z‖) (by simp)
  apply (summable_riemannXiDivisorZero_norm_inv_sq.mul_left (4 * ‖z‖ ^ 2)).of_norm_bounded_eventually
  filter_upwards [hfin.eventually_cofinite_notMem] with p hp
  have hs : ‖z‖ ≤ ‖riemannXiDivisorZeroValue p‖ / 2 := by
    have hlt : 2 * ‖z‖ < ‖riemannXiDivisorZeroValue p‖ := lt_of_not_ge hp
    linarith
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Nat.reduceAdd,
    div_eq_mul_inv, inv_pow] using norm_weierstrassFactor_div_sub_one_le_pow_div 1 hs

/-- Logarithmic moduli of the actual genus-one factors are absolutely summable. -/
theorem summable_log_norm_xi_weierstrass (z : ℂ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      Real.log ‖weierstrassFactor 1 (z / riemannXiDivisorZeroValue p)‖) := by
  simpa only [add_sub_cancel] using
    (summable_norm_xi_weierstrass_sub_one z).summable_log_norm_one_add

/-- A nonzero xi value excludes a zero in each factor of its actual product. -/
theorem xi_weierstrass_ne_zero {z : ℂ} (hz : riemannXi z ≠ 0)
    (p : RiemannXiDivisorZeroIndex) :
    weierstrassFactor 1 (z / riemannXiDivisorZeroValue p) ≠ 0 := by
  rw [ne_eq, weierstrassFactor_div_eq_zero_iff 1 (riemannXiDivisorZeroValue_ne_zero p)]
  intro he
  exact hz (he ▸ riemannXiDivisorZeroValue_eq_zero p)

/-- At nonzeros, the logarithm of the full canonical product is the sum of factor logarithms. -/
theorem log_norm_xi_canonicalProduct {z : ℂ} (hz : riemannXi z ≠ 0) :
    Real.log ‖Hadamard.divisorCanonicalProduct 1 riemannXi Set.univ z‖ =
      ∑' p : RiemannXiDivisorZeroIndex,
        Real.log ‖weierstrassFactor 1 (z / riemannXiDivisorZeroValue p)‖ := by
  have hm : Multipliable (fun p : RiemannXiDivisorZeroIndex =>
      weierstrassFactor 1 (z / riemannXiDivisorZeroValue p)) := by
    simpa only [add_sub_cancel] using
      multipliable_one_add_of_summable (summable_norm_xi_weierstrass_sub_one z)
  change Real.log ‖∏' p : RiemannXiDivisorZeroIndex,
    weierstrassFactor 1 (z / riemannXiDivisorZeroValue p)‖ = _
  rw [hm.norm_tprod, ← Real.rexp_tsum_eq_tprod
    (fun p => norm_pos_iff.mpr (xi_weierstrass_ne_zero hz p))
    (summable_log_norm_xi_weierstrass z), Real.log_exp]

end

end PrimeFactorUnimodality
