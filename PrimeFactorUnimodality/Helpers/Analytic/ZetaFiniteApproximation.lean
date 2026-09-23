import PrimeNumberTheoremAnd.ZetaBounds

/-! # An explicit finite approximation with the complete Euler remainder

The pinned PNT Euler continuation identity and its proved integral bound
give an absolute error for every positive cutoff and positive real part.
This is an analytic fallback bound, not a claim that first-order summation
is an efficient high-height evaluator. No tail is silently discarded.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- The finite terms of the existing first-order Euler continuation formula. -/
def zetaEulerApprox (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    (-N ^ (1 - s)) / (1 - s) + (-N ^ (-s)) / 2

/-- The exact discrepancy is the complete Euler integral, not a finite tail truncation. -/
theorem riemannZeta_sub_eulerApprox {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s - zetaEulerApprox N s =
      s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) := by
  rw [← Zeta0EqZeta hN hs hs1]
  dsimp [riemannZeta0, zetaEulerApprox]
  ring

/-- The audited Euler remainder supplies an explicit absolute approximation error. -/
theorem norm_riemannZeta_sub_eulerApprox_le {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - zetaEulerApprox N s‖ ≤ ‖s‖ * (N : ℝ) ^ (-s.re) / s.re := by
  rw [riemannZeta_sub_eulerApprox hN hs hs1, norm_mul]
  have h := ZetaBnd_aux1b N hN (t := s.im) hs
  rw [re_add_im] at h
  exact (mul_le_mul_of_nonneg_left h (norm_nonneg s)).trans_eq (by ring)

end

end PrimeFactorUnimodality
