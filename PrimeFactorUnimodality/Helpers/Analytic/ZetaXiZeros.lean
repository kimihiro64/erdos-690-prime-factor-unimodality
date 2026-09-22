import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiLogDerivative

set_option autoImplicit false

/-! # Geometry of xi zeros

The gamma product and the functional equation place every zero of the
entire xi function in the closed critical strip. This does not assume a
zero enumeration or a quantitative zero-free region. Inside the right
half-plane, away from one, xi and zeta have exactly the same zeros.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The extra factors in xi introduce no zeros on the open right half-plane away from one. -/
theorem riemannXi_eq_zero_iff_riemannZeta_eq_zero {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) : riemannXi s = 0 ↔ riemannZeta s = 0 := by
  rw [riemannXi_eq_shifted_gamma_product_of_re_pos hs hs1]
  have hΓ : Gamma (s / 2 + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp only [add_re, div_ofNat_re, one_re]
    linarith)
  exact mul_eq_zero.trans (or_iff_right
    (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hs1) (exp_ne_zero _)) hΓ))

/-- Xi is nonzero to the right of the critical strip. -/
theorem riemannXi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannXi s ≠ 0 := by
  intro hzero
  exact riemannZeta_ne_zero_of_one_le_re hs.le
    ((riemannXi_eq_zero_iff_riemannZeta_eq_zero (zero_lt_one.trans hs)
      (by intro h; simp [h] at hs)).mp hzero)

/-- The functional equation excludes xi zeros to the left of the critical strip. -/
theorem riemannXi_ne_zero_of_re_neg {s : ℂ} (hs : s.re < 0) : riemannXi s ≠ 0 := by
  rw [← riemannXi_one_sub s]
  exact riemannXi_ne_zero_of_one_lt_re (by simp only [sub_re, one_re]; linarith)

/-- Every xi zero belongs to the closed critical strip. -/
theorem riemannXi_zero_mem_critical_strip {ρ : ℂ} (hρ : riemannXi ρ = 0) :
    0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
  constructor
  · by_contra h
    exact riemannXi_ne_zero_of_re_neg (lt_of_not_ge h) hρ
  · by_contra h
    exact riemannXi_ne_zero_of_one_lt_re (lt_of_not_ge h) hρ

end

end PrimeFactorUnimodality
