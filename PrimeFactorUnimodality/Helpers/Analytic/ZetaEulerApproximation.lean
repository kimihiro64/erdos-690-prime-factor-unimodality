import PrimeFactorUnimodality.Helpers.Analytic.ZetaEulerTail

/-! # Arbitrary-order zeta approximation with an explicit complete error

Each extra order retains its Bernoulli boundary correction and moves the
remaining integral to a faster-decaying power. The cutoff and order are
arbitrary naturals, not a fixed finite list. This extends the exact WIP
zero-point expansion to all points of positive real part except the pole.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Polynomial

/-- The finite Euler approximation with all corrections through the given order. -/
def zetaEulerApproxOrder (N : ℕ) (s : ℂ) (m : ℕ) : ℂ :=
  zetaEulerApprox N s + ∑ j ∈ Finset.range m,
    (bernoulliNormalizedReal (j + 2) 0 : ℂ) * zetaRisingFactor s (j + 1) *
      (N : ℂ) ^ (-s - ((j + 1 : ℕ) : ℂ))

/-- Complete absolute error budget, with a finite rational Bernoulli majorant. -/
def zetaEulerError (N : ℕ) (s : ℂ) (m : ℕ) : ℝ :=
  (bernoulliCoeffBound (m + 1) : ℝ) * ‖zetaRisingFactor s (m + 1)‖ *
    (N : ℝ) ^ (-s.re - (m : ℝ)) / (s.re + (m : ℝ))

/-- Exact Euler expansion at every finite order, including the full residual tail. -/
theorem riemannZeta_sub_eulerApproxOrder {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (m : ℕ) :
    riemannZeta s - zetaEulerApproxOrder N s m =
      -zetaRisingFactor s (m + 1) * zetaEulerTail N s (m + 1) := by
  induction m with
  | zero =>
    simpa only [zetaEulerApproxOrder, zetaRisingFactor, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
      add_zero, one_mul] using riemannZeta_sub_eulerApprox_eq_tail hN hs hs1
  | succ m ih =>
    dsimp only [zetaEulerApproxOrder] at ih ⊢
    rw [Finset.sum_range_succ, zetaRisingFactor_succ s (m + 1)]
    rw [zetaEulerTail_recursion hN (show 1 ≤ m + 1 by omega) hs] at ih
    linear_combination ih

/-- The complete Euler approximation has an explicit error for arbitrary cutoff and order. -/
theorem norm_riemannZeta_sub_eulerApproxOrder_le {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (m : ℕ) :
    ‖riemannZeta s - zetaEulerApproxOrder N s m‖ ≤ zetaEulerError N s m := by
  rw [riemannZeta_sub_eulerApproxOrder hN hs hs1, norm_mul, norm_neg]
  exact (mul_le_mul_of_nonneg_left (norm_zetaEulerTail_le hN hs m)
    (norm_nonneg _)).trans_eq (by dsimp [zetaEulerError]; ring)

/-- The explicit error is nonnegative in the half-plane where it is used. -/
theorem zetaEulerError_nonneg (N m : ℕ) {s : ℂ} (hs : 0 < s.re) :
    0 ≤ zetaEulerError N s m := by
  have hB : (0 : ℝ) ≤ (bernoulliCoeffBound (m + 1) : ℝ) := by
    exact_mod_cast bernoulliCoeffBound_nonneg (m + 1)
  unfold zetaEulerError
  positivity

end

end PrimeFactorUnimodality
