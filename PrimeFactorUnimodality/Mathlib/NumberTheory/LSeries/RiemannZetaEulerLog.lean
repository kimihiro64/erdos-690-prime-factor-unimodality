/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Tactic.Linarith

/-! # An analytic Euler logarithm of the Riemann zeta function

The Dirichlet series with coefficients `Lambda(n)/log(n)` is an analytic
logarithm of zeta on `Re(s)>1`. Its nonnegative coefficients bound its norm
on a vertical line by `log(norm(zeta(sigma)))`. This is a genuine continuous
logarithm, rather than a claim that the principal logarithm follows zeta's
argument. The Euler-product identities and L-series differentiation are
reused directly from Mathlib.
-/

open Complex ArithmeticFunction
open scoped Topology

/-- The Euler logarithm of zeta, represented by its von Mangoldt Dirichlet series. -/
noncomputable def riemannZetaEulerLog (s : ℂ) : ℂ :=
  LSeries (fun n => (vonMangoldt n : ℂ) / Real.log n) s

private lemma norm_eulerLog_coeff_le (n : ℕ) :
    ‖(vonMangoldt n : ℂ) / Real.log n‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg, abs_of_nonneg (Real.log_natCast_nonneg n)]
  exact div_le_one_of_le₀ vonMangoldt_le_log (Real.log_natCast_nonneg n)

private lemma eulerLog_abscissa_le :
    LSeries.abscissaOfAbsConv (fun n => (vonMangoldt n : ℂ) / Real.log n) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => norm_eulerLog_coeff_le n⟩

/-- Absolute convergence of the Euler-logarithm series on the right half-plane. -/
theorem summable_riemannZetaEulerLog {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (vonMangoldt n : ℂ) / Real.log n) s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re
    (eulerLog_abscissa_le.trans_lt (by exact_mod_cast hs))

/-- The Euler-product logarithm exponentiates to zeta. -/
theorem exp_riemannZetaEulerLog {s : ℂ} (hs : 1 < s.re) :
    exp (riemannZetaEulerLog s) = riemannZeta s := by
  have hc (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  have h := DirichletCharacter.eulerProduct_log_eq_LSeries (1 : DirichletCharacter ℂ 1) hs
  simp only [hc, one_mul] at h
  unfold riemannZetaEulerLog
  rw [← h]
  exact riemannZeta_eulerProduct_exp_log hs

/-- Differentiability follows from the existing L-series theorem. -/
theorem differentiableAt_riemannZetaEulerLog {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ riemannZetaEulerLog s :=
  (LSeries_hasDerivAt (eulerLog_abscissa_le.trans_lt (by exact_mod_cast hs))).differentiableAt

open scoped ComplexOrder in
private lemma eulerLog_coeff_nonneg (n : ℕ) : 0 ≤ (vonMangoldt n : ℂ) / Real.log n := by
  rw [← ofReal_div, zero_le_real]
  exact div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)

open scoped ComplexOrder in
/-- The Euler logarithm is nonnegative real on the real axis. -/
theorem riemannZetaEulerLog_ofReal_nonneg (σ : ℝ) : 0 ≤ riemannZetaEulerLog σ := by
  exact tsum_nonneg (fun n => LSeries.term_nonneg (eulerLog_coeff_nonneg n) σ)

/-- The real-axis Euler logarithm has zero imaginary part. -/
theorem riemannZetaEulerLog_ofReal_im (σ : ℝ) : (riemannZetaEulerLog σ).im = 0 :=
  (Complex.nonneg_iff.mp (riemannZetaEulerLog_ofReal_nonneg σ)).2.symm

/-- The real part of this logarithm is the logarithm of zeta's modulus. -/
theorem re_riemannZetaEulerLog {s : ℂ} (hs : 1 < s.re) :
    (riemannZetaEulerLog s).re = Real.log ‖riemannZeta s‖ := by
  rw [← exp_riemannZetaEulerLog hs, norm_exp, Real.log_exp]

open scoped ComplexOrder in
/-- Nonnegative Dirichlet coefficients give a sharp real-axis majorant. -/
theorem norm_riemannZetaEulerLog_le {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZetaEulerLog s‖ ≤ Real.log ‖riemannZeta (s.re : ℂ)‖ := by
  rw [← re_riemannZetaEulerLog (show 1 < (s.re : ℂ).re from hs)]
  unfold riemannZetaEulerLog
  rw [LSeries, LSeries, re_tsum (summable_riemannZetaEulerLog
    (show 1 < (s.re : ℂ).re from hs))]
  calc
    _ ≤ ∑' n, ‖LSeries.term (fun n => (vonMangoldt n : ℂ) / Real.log n) s n‖ :=
      norm_tsum_le_tsum_norm (summable_riemannZetaEulerLog hs).norm
    _ = _ := by
      apply tsum_congr
      intro n
      have hn := LSeries.term_nonneg
        (a := fun k => (vonMangoldt k : ℂ) / Real.log k) (n := n)
        (eulerLog_coeff_nonneg n) s.re
      have he := congrArg Complex.re (Complex.eq_coe_norm_of_nonneg hn)
      simp only [ofReal_re] at he
      rw [he]
      simp only [LSeries.norm_term_eq, ofReal_re]

/-- In particular the Euler argument is uniformly bounded along each vertical line. -/
theorem abs_im_riemannZetaEulerLog_le {s : ℂ} (hs : 1 < s.re) :
    |(riemannZetaEulerLog s).im| ≤ Real.log ‖riemannZeta (s.re : ℂ)‖ :=
  (abs_im_le_norm _).trans (norm_riemannZetaEulerLog_le hs)

/-- The Euler logarithm also supplies a lower modulus bound on a vertical line. -/
theorem inv_norm_riemannZeta_real_le {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta (s.re : ℂ)‖⁻¹ ≤ ‖riemannZeta s‖ := by
  have hreal : 0 < ‖riemannZeta (s.re : ℂ)‖ := by
    rw [← exp_riemannZetaEulerLog (show 1 < (s.re : ℂ).re from hs), norm_exp]
    exact Real.exp_pos _
  have hre : -Real.log ‖riemannZeta (s.re : ℂ)‖ ≤ (riemannZetaEulerLog s).re := by
    have hn := norm_riemannZetaEulerLog_le hs
    have hl := neg_abs_le (riemannZetaEulerLog s).re
    have ha := abs_re_le_norm (riemannZetaEulerLog s)
    linarith
  calc
    _ = Real.exp (-Real.log ‖riemannZeta (s.re : ℂ)‖) := by
      rw [Real.exp_neg, Real.exp_log hreal]
    _ ≤ Real.exp (riemannZetaEulerLog s).re := Real.exp_le_exp.mpr hre
    _ = ‖riemannZeta s‖ := by rw [← norm_exp, exp_riemannZetaEulerLog hs]

/-- The derivative of the Euler logarithm is the actual zeta logarithmic derivative. -/
theorem deriv_riemannZetaEulerLog {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZetaEulerLog s = logDeriv riemannZeta s := by
  have he : (fun z => exp (riemannZetaEulerLog z)) =ᶠ[𝓝 s] riemannZeta := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact exp_riemannZetaEulerLog hz
  have hd := ((hasDerivAt_exp (riemannZetaEulerLog s)).comp s
    (differentiableAt_riemannZetaEulerLog hs).hasDerivAt).congr_of_eventuallyEq he.symm
  rw [logDeriv_apply, hd.deriv, ← exp_riemannZetaEulerLog hs]
  exact (mul_div_cancel_left₀ _ (exp_ne_zero _)).symm

/-- The positive real Euler majorant also bounds the modulus of zeta itself. -/
theorem norm_riemannZeta_le_norm_real {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ := by
  have hp : 0 < ‖riemannZeta (s.re : ℂ)‖ := by
    rw [← exp_riemannZetaEulerLog (show 1 < (s.re : ℂ).re from hs), norm_exp]
    exact Real.exp_pos _
  rw [← exp_riemannZetaEulerLog hs, norm_exp, ← Real.exp_log hp]
  exact Real.exp_le_exp.mpr ((re_le_norm _).trans (norm_riemannZetaEulerLog_le hs))
