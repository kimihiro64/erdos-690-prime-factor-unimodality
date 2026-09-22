import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import PrimeFactorUnimodality.Helpers.Analytic.StechkinBasic
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiZeroContribution

set_option autoImplicit false

/-! # The full xi zero sum in Stechkin's inequality

Subtract the Hadamard expansions at `s` and `1-conj s`. Xi symmetry
identifies their difference as twice its real logarithmic derivative.
The summable difference is precisely the reflected Poisson kernel, so
Stechkin positivity passes to the whole multiplicity-carrying divisor sum
without choosing an enumeration or assuming a pairing bijection.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter
open scoped BigOperators ComplexConjugate Topology

private theorem xi_conj_of_re_pos {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    riemannXi (conj s) = conj (riemannXi s) := by
  have hc₁ : conj s ≠ 1 := by
    intro h
    apply hs₁
    simpa using congrArg (starRingEnd ℂ) h
  rw [riemannXi_eq_shifted_gamma_product_of_re_pos (by simpa using hs) hc₁,
    riemannXi_eq_shifted_gamma_product_of_re_pos hs hs₁]
  simp only [map_mul, map_sub, map_one, ← riemannZeta_conj, ← Gamma_conj,
    ← exp_conj, map_neg, map_div₀, map_ofNat, map_add, conj_ofReal]

/-- Xi respects conjugation on the whole complex plane, including its zeros. -/
theorem riemannXi_conj (s : ℂ) : riemannXi (conj s) = conj (riemannXi s) := by
  by_cases h₀ : s = 0
  · simp [h₀, riemannXi_zero, map_ofNat]
  by_cases h₁ : s = 1
  · have hx₁ : riemannXi 1 = 1 / 2 := by
      simpa using (riemannXi_one_sub 0).trans riemannXi_zero
    simp [h₁, hx₁, map_ofNat]
  by_cases hs : 0 < s.re
  · exact xi_conj_of_re_pos hs h₁
  have ht : 0 < (1 - s).re := by simp only [sub_re, one_re]; linarith
  have ht₁ : 1 - s ≠ 1 := by intro h; apply h₀; linear_combination -h
  have h := xi_conj_of_re_pos ht ht₁
  simpa only [map_sub, map_one, riemannXi_one_sub] using h

/-- Reflection across the critical line preserves actual xi zeros. -/
theorem riemannXi_reflected_zero {ρ : ℂ} (hρ : riemannXi ρ = 0) :
    riemannXi (1 - conj ρ) = 0 := by
  rw [riemannXi_one_sub, riemannXi_conj, hρ, map_zero]

/-- Conjugation symmetry in the half-plane where the shifted gamma product is available. -/
theorem riemannXi_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannXi (conj s) = conj (riemannXi s) := by
  rw [riemannXi_eq_shifted_gamma_product (by simpa using hs),
    riemannXi_eq_shifted_gamma_product hs]
  simp only [map_mul, map_sub, map_one, ← riemannZeta_conj, ← Gamma_conj,
    ← exp_conj, map_neg, map_div₀, map_ofNat, map_add, conj_ofReal]

/-- The logarithmic derivative respects conjugation to the right of the critical strip. -/
theorem logDeriv_riemannXi_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannXi (conj s) = conj (logDeriv riemannXi s) := by
  have heq : (conj ∘ riemannXi ∘ conj) =ᶠ[𝓝 s] riemannXi := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    simp only [Function.comp_apply, riemannXi_conj_of_one_lt_re hz, conj_conj]
  have hd := ((differentiable_riemannXi (conj s)).hasDerivAt.conj_conj)
  simp only [conj_conj] at hd
  have hd' := (hd.congr_of_eventuallyEq heq.symm).deriv
  have hderiv : deriv riemannXi (conj s) = conj (deriv riemannXi s) := by
    rw [hd', conj_conj]
  simp only [logDeriv_apply, hderiv, riemannXi_conj_of_one_lt_re hs, map_div₀]

/-- Differentiating the xi functional equation negates its logarithmic derivative. -/
theorem logDeriv_riemannXi_one_sub (s : ℂ) :
    logDeriv riemannXi (1 - s) = -logDeriv riemannXi s := by
  have hd := ((differentiable_riemannXi (1 - s)).hasDerivAt).comp s
    ((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s))
  have heq : (fun z : ℂ => riemannXi (1 - z)) = riemannXi :=
    funext riemannXi_one_sub
  change HasDerivAt (fun z : ℂ => riemannXi (1 - z))
    (deriv riemannXi (1 - s) * (0 - 1)) s at hd
  rw [heq] at hd
  have hderiv : deriv riemannXi s = -deriv riemannXi (1 - s) := by
    simpa using hd.deriv
  simp only [logDeriv_apply, riemannXi_one_sub, hderiv, neg_div, neg_neg]

private theorem xi_point_ne_zero_value {s : ℂ} (hs : riemannXi s ≠ 0)
    (p : RiemannXiDivisorZeroIndex) : s ≠ riemannXiDivisorZeroValue p :=
  fun h => hs (h ▸ riemannXiDivisorZeroValue_eq_zero p)

private theorem xi_pair_term_eq (s ρ : ℂ) :
    (1 / (s - ρ) + 1 / ρ).re - (1 / (1 - conj s - ρ) + 1 / ρ).re =
      stechkinZeroPair s ρ := by
  have heq : 1 - conj s - ρ = -conj (s - 1 + conj ρ) := by
    simp only [map_add, map_sub, map_one, conj_conj]
    ring
  rw [heq]
  simp only [stechkinZeroPair, one_div, inv_neg, ← map_inv₀, add_re, neg_re, conj_re]
  ring

/-- The real reflected-zero kernels form an absolutely convergent series. -/
theorem summable_stechkinZeroPair {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      stechkinZeroPair s (riemannXiDivisorZeroValue p)) := by
  have hs₀ := riemannXi_ne_zero_of_one_lt_re hs
  have hs₁ : riemannXi (1 - conj s) ≠ 0 := by
    rw [riemannXi_one_sub]
    exact riemannXi_ne_zero_of_one_lt_re (by simpa using hs)
  have h₀ := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ (xi_point_ne_zero_value hs₀)
  have h₁ := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ (xi_point_ne_zero_value hs₁)
  simpa only [sub_re, xi_pair_term_eq] using
    (Complex.hasSum_re (h₀.sub h₁).hasSum).summable

/-- Symmetrizing the Hadamard expansion removes its constant and preserves multiplicities. -/
theorem two_re_logDeriv_riemannXi_eq_tsum_pair {s : ℂ} (hs : 1 < s.re) :
    2 * (logDeriv riemannXi s).re =
      ∑' p : RiemannXiDivisorZeroIndex, stechkinZeroPair s (riemannXiDivisorZeroValue p) := by
  have hs₀ := riemannXi_ne_zero_of_one_lt_re hs
  have hs₁ : riemannXi (1 - conj s) ≠ 0 := by
    rw [riemannXi_one_sub]
    exact riemannXi_ne_zero_of_one_lt_re (by simpa using hs)
  have h₀ := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ (xi_point_ne_zero_value hs₀)
  have h₁ := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ (xi_point_ne_zero_value hs₁)
  have heq : logDeriv riemannXi s - logDeriv riemannXi (1 - conj s) =
      ∑' p : RiemannXiDivisorZeroIndex,
        ((1 / (s - riemannXiDivisorZeroValue p) + 1 / riemannXiDivisorZeroValue p) -
          (1 / (1 - conj s - riemannXiDivisorZeroValue p) +
            1 / riemannXiDivisorZeroValue p)) := by
    rw [logDeriv_riemannXi_eq_zero_add_tsum_of_ne_zero hs₀,
      logDeriv_riemannXi_eq_zero_add_tsum_of_ne_zero hs₁, h₀.tsum_sub h₁]
    ring
  have h := congrArg Complex.re heq
  rw [logDeriv_riemannXi_one_sub, logDeriv_riemannXi_conj_of_one_lt_re hs,
    re_tsum (h₀.sub h₁)] at h
  simp only [sub_re, neg_re, conj_re, xi_pair_term_eq] at h
  linarith

/-- Stechkin positivity holds for the full xi logarithmic derivative. -/
theorem re_logDeriv_riemannXi_stechkin_nonneg {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ (logDeriv riemannXi ((σ : ℂ) + t * I)).re -
      (1 / Real.sqrt 5) *
        (logDeriv riemannXi ((Real.stechkinShift σ : ℂ) + t * I)).re := by
  have hτ := (Real.stechkinShift_spec hσ).1
  have hs : 1 < (((σ : ℂ) + t * I)).re := by simpa using hσ
  have hs₁ : 1 < (((Real.stechkinShift σ : ℂ) + t * I)).re := by simpa using hτ
  have hsum : 0 ≤ ∑' p : RiemannXiDivisorZeroIndex,
      (stechkinZeroPair ((σ : ℂ) + t * I) (riemannXiDivisorZeroValue p) -
        (1 / Real.sqrt 5) * stechkinZeroPair
          ((Real.stechkinShift σ : ℂ) + t * I) (riemannXiDivisorZeroValue p)) :=
    tsum_nonneg (fun p =>
      stechkinZeroPair_sub_nonneg hσ (riemannXiDivisorZeroValue_eq_zero p) t)
  rw [(summable_stechkinZeroPair hs).tsum_sub
    ((summable_stechkinZeroPair hs₁).mul_left (1 / Real.sqrt 5)), tsum_mul_left,
    ← two_re_logDeriv_riemannXi_eq_tsum_pair hs,
    ← two_re_logDeriv_riemannXi_eq_tsum_pair hs₁] at hsum
  linarith

end

end PrimeFactorUnimodality
