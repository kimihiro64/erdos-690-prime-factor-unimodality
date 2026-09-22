import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiZeroContribution
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Hadamard.Integral
import PrimeNumberTheoremAnd.IEANTN.RobinXiZeroSummability

/-! # Absolute contour interchange for the actual xi divisor

The order-one fractional moment and the closed critical strip justify
integrating the entire multiplicity-indexed Hadamard expansion. The moment
is `summable_riemannXiDivisorZero_norm_inv_rpow` from the Apache-2.0 PNT
repository at `f6147e7572ab3abe5428101bc0b13627bcb005df`; its proof uses
entire growth, not a hypothesis locating zeros on the critical line.
If the weight has integral zero, the Hadamard constant cancels exactly.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory

private instance : Countable RiemannXiDivisorZeroIndex := by
  have hc := (summable_riemannXiDivisorZero_norm_inv_rpow
    (a := (3 / 2 : ℝ)) (by norm_num)).countable_support
  have heq : Function.support (fun p : RiemannXiDivisorZeroIndex =>
      ‖riemannXiDivisorZeroValue p‖⁻¹ ^ (3 / 2 : ℝ)) = Set.univ := by
    ext p
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos
      (inv_pos.mpr (norm_pos_iff.mpr (riemannXiDivisorZeroValue_ne_zero p))) _).ne'
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc

/-- Absolute integrated norms over all xi zeros, with their actual multiplicities. -/
theorem summable_integral_norm_mul_xi_hadamardAtoms
    {c C : ℝ} (hc : 1 < c) (hC : 0 ≤ C) {H : ℝ → ℂ} (hH : Integrable H)
    (hBound : ∀ t, ‖H t‖ ≤ C / ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2) :
    Summable (fun p : RiemannXiDivisorZeroIndex => ∫ t : ℝ,
      ‖H t * (1 / ((c : ℂ) + (t : ℂ) * I - riemannXiDivisorZeroValue p) +
        1 / riemannXiDivisorZeroValue p)‖) :=
  summable_integral_norm_mul_hadamardAtoms (by linarith) hc hC
    riemannXiDivisorZeroValue_ne_zero
    (fun p => (riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)).2)
    (summable_riemannXiDivisorZero_norm_inv_rpow (by norm_num)) hH hBound

/-- The whole weighted xi zero series, rather than only individual terms, is integrable. -/
theorem integrable_mul_tsum_xi_hadamardAtoms
    {c C : ℝ} (hc : 1 < c) (hC : 0 ≤ C) {H : ℝ → ℂ} (hH : Integrable H)
    (hBound : ∀ t, ‖H t‖ ≤ C / ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2) :
    Integrable (fun t : ℝ => H t * (∑' p : RiemannXiDivisorZeroIndex,
      (1 / ((c : ℂ) + (t : ℂ) * I - riemannXiDivisorZeroValue p) +
        1 / riemannXiDivisorZeroValue p))) :=
  integrable_mul_tsum_hadamardAtoms (by linarith) hc hC
    riemannXiDivisorZeroValue_ne_zero
    (fun p => (riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)).2)
    (summable_riemannXiDivisorZero_norm_inv_rpow (by norm_num)) hH hBound

/-- Interchange the complete xi series and the contour integral. -/
theorem tsum_integral_mul_xi_hadamardAtoms
    {c C : ℝ} (hc : 1 < c) (hC : 0 ≤ C) {H : ℝ → ℂ} (hH : Integrable H)
    (hBound : ∀ t, ‖H t‖ ≤ C / ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2) :
    (∑' p : RiemannXiDivisorZeroIndex, ∫ t : ℝ,
      H t * (1 / ((c : ℂ) + (t : ℂ) * I - riemannXiDivisorZeroValue p) +
        1 / riemannXiDivisorZeroValue p)) =
      ∫ t : ℝ, H t * (∑' p : RiemannXiDivisorZeroIndex,
        (1 / ((c : ℂ) + (t : ℂ) * I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)) :=
  tsum_integral_mul_hadamardAtoms (by linarith) hc hC
    riemannXiDivisorZeroValue_ne_zero
    (fun p => (riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)).2)
    (summable_riemannXiDivisorZero_norm_inv_rpow (by norm_num)) hH hBound

/-- The integrated xi logarithmic derivative equals the integrated regularized zero series. -/
theorem integral_mul_logDeriv_riemannXi_eq_tsum
    {c C : ℝ} (hc : 1 < c) (hC : 0 ≤ C) {H : ℝ → ℂ} (hH : Integrable H)
    (hBound : ∀ t, ‖H t‖ ≤ C / ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2)
    (hZero : (∫ t : ℝ, H t) = 0) :
    (∫ t : ℝ, H t * logDeriv riemannXi ((c : ℂ) + (t : ℂ) * I)) =
      ∑' p : RiemannXiDivisorZeroIndex, ∫ t : ℝ,
        H t * (1 / ((c : ℂ) + (t : ℂ) * I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p) := by
  rw [tsum_integral_mul_xi_hadamardAtoms hc hC hH hBound]
  have heq (t : ℝ) := logDeriv_riemannXi_eq_zero_add_tsum
    (s := (c : ℂ) + (t : ℂ) * I) (by simpa using hc)
  simp_rw [heq, mul_add]
  rw [integral_add (hH.mul_const _) (integrable_mul_tsum_xi_hadamardAtoms hc hC hH hBound),
    integral_mul_const, hZero, zero_mul, zero_add]

end

end PrimeFactorUnimodality
