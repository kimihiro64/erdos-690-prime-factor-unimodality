import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiZeros
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannXiDivisorZeros

set_option autoImplicit false

/-! # Individual zero contributions to the xi logarithmic derivative

Use the genus-one Hadamard factorization with its actual divisor index,
including multiplicities. Evaluating at zero identifies the constant as
`logDeriv riemannXi 0`. The closed critical strip makes every real summand
nonnegative to its right; retaining one zero gives its explicit pole term.

The factorization and summability primitives are Matteo Cipollina's
Apache-2.0 `RiemannZetaHadamard` and `RiemannXiDivisorZeros` from
`kimihiro64/PrimeNumberTheoremAnd` at revision
`f6147e7572ab3abe5428101bc0b13627bcb005df`, with the reproducible API-only
ports in `scripts/patch_pnt_compat.py`. No zero-sum identity is assumed.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex
open scoped BigOperators

private theorem xi_point_ne_divisor_zero {s : ℂ} (hs : 1 < s.re)
    (p : RiemannXiDivisorZeroIndex) : s ≠ riemannXiDivisorZeroValue p := by
  intro h
  exact riemannXi_ne_zero_of_one_lt_re hs (h ▸ riemannXiDivisorZeroValue_eq_zero p)

/-- Every actual xi zero occurs in the divisor index used by the Hadamard sum. -/
theorem exists_xi_divisor_index_of_zero {ρ : ℂ} (hρ : riemannXi ρ = 0) :
    ∃ p : RiemannXiDivisorZeroIndex, riemannXiDivisorZeroValue p = ρ := by
  have hρ0 : ρ ≠ 0 := by intro h; subst h; norm_num [riemannXi_zero] at hρ
  have htop := Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero
    differentiable_riemannXi riemannXi_nontrivial ρ
  have hn : analyticOrderNatAt riemannXi ρ ≠ 0 := by
    intro hn
    have he : analyticOrderAt riemannXi ρ = 0 := by
      rw [← Nat.cast_analyticOrderNatAt htop, hn, Nat.cast_zero]
    exact ((differentiable_riemannXi.analyticAt ρ).analyticOrderAt_eq_zero.mp he) hρ
  have hcard := Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    (hf := differentiable_riemannXi) hρ0
  have hpos : 0 < (Hadamard.divisorZeroIndex₀_fiberFinset (f := riemannXi) ρ).card := by
    rw [hcard]
    exact Nat.pos_of_ne_zero hn
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  exact ⟨p, (Hadamard.mem_divisorZeroIndex₀_fiberFinset (f := riemannXi) (z₀ := ρ) p).mp hp⟩

/-- The Hadamard constant equals the logarithmic derivative at the origin. -/
theorem logDeriv_riemannXi_eq_zero_add_tsum {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannXi s = logDeriv riemannXi 0 +
      ∑' p : RiemannXiDivisorZeroIndex,
        (1 / (s - riemannXiDivisorZeroValue p) + 1 / riemannXiDivisorZeroValue p) := by
  obtain ⟨P, hdeg, hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  have h0 := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
    (z := 0) hfac (fun p => (riemannXiDivisorZeroValue_ne_zero p).symm)
  have hc : Polynomial.eval s P.derivative = Polynomial.eval 0 P.derivative := by
    rw [P.eq_X_add_C_of_degree_le_one hdeg]
    simp
  have h0' : logDeriv riemannXi 0 = Polynomial.eval 0 P.derivative := by
    simpa only [zero_sub, one_div, inv_neg, neg_add_cancel, tsum_zero, add_zero] using h0
  rw [logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac
    (xi_point_ne_divisor_zero hs), hc, ← h0']

private theorem re_xi_zero_term_nonneg {s : ℂ} (hs : 1 < s.re)
    (p : RiemannXiDivisorZeroIndex) :
    0 ≤ (1 / (s - riemannXiDivisorZeroValue p) + 1 / riemannXiDivisorZeroValue p).re := by
  obtain ⟨hlo, hhi⟩ := riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)
  rw [add_re, one_div, one_div, inv_re, inv_re]
  exact add_nonneg (div_nonneg (by simp only [sub_re]; linarith) (normSq_nonneg _))
    (div_nonneg hlo (normSq_nonneg _))

/-- Dropping all nonnegative real zero contributions leaves the Hadamard constant. -/
theorem re_logDeriv_riemannXi_zero_le {s : ℂ} (hs : 1 < s.re) :
    (logDeriv riemannXi 0).re ≤ (logDeriv riemannXi s).re := by
  rw [logDeriv_riemannXi_eq_zero_add_tsum hs, add_re,
    re_tsum (summable_riemannXi_logDerivTerms_divisorZeroIndex₀ (xi_point_ne_divisor_zero hs))]
  exact le_add_of_nonneg_right (tsum_nonneg (re_xi_zero_term_nonneg hs))

/-- Retain one divisor-indexed zero without losing its multiplicity or sign. -/
theorem re_logDeriv_riemannXi_single_zero_le {s : ℂ} (hs : 1 < s.re)
    (p : RiemannXiDivisorZeroIndex) :
    (logDeriv riemannXi 0).re +
      (1 / (s - riemannXiDivisorZeroValue p)).re ≤ (logDeriv riemannXi s).re := by
  have hsum := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ (xi_point_ne_divisor_zero hs)
  have hreal := (Complex.hasSum_re hsum.hasSum).summable
  have hterm := hreal.le_tsum p (fun q _ => re_xi_zero_term_nonneg hs q)
  have hρ := (riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)).1
  have hcorrection : 0 ≤ (1 / riemannXiDivisorZeroValue p).re := by
    rw [one_div, inv_re]
    exact div_nonneg hρ (normSq_nonneg _)
  rw [logDeriv_riemannXi_eq_zero_add_tsum hs, add_re, re_tsum hsum]
  simp only [add_re] at hterm ⊢
  linarith

/-- At the height of a zero, its real pole contribution is exactly `1/(σ-β)`. -/
theorem re_logDeriv_riemannXi_aligned_zero_le {σ : ℝ} (hσ : 1 < σ)
    (p : RiemannXiDivisorZeroIndex) :
    (logDeriv riemannXi 0).re + 1 / (σ - (riemannXiDivisorZeroValue p).re) ≤
      (logDeriv riemannXi ((σ : ℂ) + (riemannXiDivisorZeroValue p).im * I)).re := by
  have h := re_logDeriv_riemannXi_single_zero_le
    (s := (σ : ℂ) + (riemannXiDivisorZeroValue p).im * I) (by simpa using hσ) p
  have heq : (σ : ℂ) + (riemannXiDivisorZeroValue p).im * I - riemannXiDivisorZeroValue p =
      ((σ - (riemannXiDivisorZeroValue p).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [heq, ← ofReal_one, ← ofReal_div, ofReal_re] at h
  exact h

/-- Zeta at a zero's height: gamma and pole bounds minus the explicit zero contribution. -/
theorem re_neg_logDeriv_riemannZeta_le_single_zero {σ : ℝ} (hσ : 1 < σ) (hσ₂ : σ ≤ 2)
    (p : RiemannXiDivisorZeroIndex) :
    (-deriv riemannZeta ((σ : ℂ) + (riemannXiDivisorZeroValue p).im * I) /
      riemannZeta ((σ : ℂ) + (riemannXiDivisorZeroValue p).im * I)).re ≤
      -(logDeriv riemannXi 0).re - 1 / (σ - (riemannXiDivisorZeroValue p).re) +
        (1 / ((σ : ℂ) + (riemannXiDivisorZeroValue p).im * I - 1)).re +
          ((1 / 2 : ℝ) * Real.log (|(riemannXiDivisorZeroValue p).im| / 2 + 3) + 1 / 2 -
            (1 / 2 : ℝ) * Real.log Real.pi) := by
  have h := re_neg_logDeriv_riemannZeta_le_xi
    (s := (σ : ℂ) + (riemannXiDivisorZeroValue p).im * I)
    (by simpa using hσ) (by simpa using hσ₂)
  have hz := re_logDeriv_riemannXi_aligned_zero_le hσ p
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
    zero_add, add_zero] at h
  linarith

/-- Exact real Hadamard constant; no unspecified constant remains in the zero bound. -/
theorem re_logDeriv_riemannXi_zero_eq :
    (logDeriv riemannXi 0).re =
      (Real.log (4 * Real.pi) - Real.eulerMascheroniConstant - 2) / 2 := by
  have h := congrArg Complex.re neg_two_mul_logDeriv_riemannXi_zero_eq
  norm_num [mul_re] at h
  linarith

/-- The single-zero bound applies to every actual xi zero, not only a supplied index. -/
theorem re_neg_logDeriv_riemannZeta_le_zero {ρ : ℂ} (hρ : riemannXi ρ = 0)
    {σ : ℝ} (hσ : 1 < σ) (hσ₂ : σ ≤ 2) :
    (-deriv riemannZeta ((σ : ℂ) + ρ.im * I) /
      riemannZeta ((σ : ℂ) + ρ.im * I)).re ≤
      -(logDeriv riemannXi 0).re - 1 / (σ - ρ.re) +
        (1 / ((σ : ℂ) + ρ.im * I - 1)).re +
          ((1 / 2 : ℝ) * Real.log (|ρ.im| / 2 + 3) + 1 / 2 -
            (1 / 2 : ℝ) * Real.log Real.pi) := by
  obtain ⟨p, hp⟩ := exists_xi_divisor_index_of_zero hρ
  simpa [hp] using re_neg_logDeriv_riemannZeta_le_single_zero hσ hσ₂ p

end

end PrimeFactorUnimodality
