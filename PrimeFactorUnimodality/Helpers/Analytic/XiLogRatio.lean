import PrimeFactorUnimodality.Helpers.Analytic.XiCanonicalLog

/-! # Exact unit-step logarithmic ratios of xi

Taking log moduli of the actual Hadamard product gives an absolutely
convergent difference series. The real linear factor cancels the real
reciprocal-zero sum, leaving only logarithmic distances to the zeros.
Only the two endpoint values must be nonzero, not the intervening segment.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

private theorem log_norm_xi_factor {z : ℂ} (hz : riemannXi z ≠ 0)
    (p : RiemannXiDivisorZeroIndex) :
    Real.log ‖weierstrassFactor 1 (z / riemannXiDivisorZeroValue p)‖ =
      Real.log ‖z - riemannXiDivisorZeroValue p‖ -
        Real.log ‖riemannXiDivisorZeroValue p‖ + (z / riemannXiDivisorZeroValue p).re := by
  let r := riemannXiDivisorZeroValue p
  have hr : r ≠ 0 := riemannXiDivisorZeroValue_ne_zero p
  have hzr : z - r ≠ 0 := by
    intro he
    exact hz ((sub_eq_zero.mp he) ▸ riemannXiDivisorZeroValue_eq_zero p)
  have he : 1 - z / r = -(z - r) / r := by field_simp; ring
  simp only [weierstrassFactor_def, partialLogSum_eq_sum, Finset.sum_range_one,
    zero_add, pow_one, Nat.cast_zero, div_one]
  change Real.log ‖(1 - z / r) * exp (z / r)‖ = _
  rw [he, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (div_ne_zero (neg_ne_zero.mpr hzr) hr))
    (norm_ne_zero_iff.mpr (exp_ne_zero _)), norm_div, norm_neg,
    Real.log_div (norm_ne_zero_iff.mpr hzr) (norm_ne_zero_iff.mpr hr),
    norm_exp, Real.log_exp]

private theorem xi_factor_log_step {z : ℂ} (hz : riemannXi z ≠ 0)
    (hz1 : riemannXi (z + 1) ≠ 0) (p : RiemannXiDivisorZeroIndex) :
    Real.log ‖weierstrassFactor 1 ((z + 1) / riemannXiDivisorZeroValue p)‖ -
      Real.log ‖weierstrassFactor 1 (z / riemannXiDivisorZeroValue p)‖ =
    (Real.log ‖z + 1 - riemannXiDivisorZeroValue p‖ -
      Real.log ‖z - riemannXiDivisorZeroValue p‖) + (1 / riemannXiDivisorZeroValue p).re := by
  rw [log_norm_xi_factor hz1, log_norm_xi_factor hz, add_div, add_re]
  ring

/-- Unit-step differences of the unregularized log moduli form an absolutely convergent series. -/
theorem summable_xi_log_distance_step {z : ℂ} (hz : riemannXi z ≠ 0)
    (hz1 : riemannXi (z + 1) ≠ 0) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      Real.log ‖z + 1 - riemannXiDivisorZeroValue p‖ -
        Real.log ‖z - riemannXiDivisorZeroValue p‖) := by
  apply (((summable_log_norm_xi_weierstrass (z + 1)).sub
    (summable_log_norm_xi_weierstrass z)).sub summable_re_xi_divisor_reciprocal).congr
  intro p
  rw [xi_factor_log_step hz hz1]
  ring

/-- The exact xi log-modulus increment equals the full multiplicity-counted distance series. -/
theorem log_norm_riemannXi_step_eq_tsum {z : ℂ} (hz : riemannXi z ≠ 0)
    (hz1 : riemannXi (z + 1) ≠ 0) :
    Real.log ‖riemannXi (z + 1)‖ - Real.log ‖riemannXi z‖ =
      ∑' p : RiemannXiDivisorZeroIndex,
        (Real.log ‖z + 1 - riemannXiDivisorZeroValue p‖ -
          Real.log ‖z - riemannXiDivisorZeroValue p‖) := by
  obtain ⟨P, hdeg, hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  have hlog (s : ℂ) (hs : riemannXi s ≠ 0) :
      Real.log ‖riemannXi s‖ = (P.eval s).re +
        ∑' p : RiemannXiDivisorZeroIndex,
          Real.log ‖weierstrassFactor 1 (s / riemannXiDivisorZeroValue p)‖ := by
    have hp : Hadamard.divisorCanonicalProduct 1 riemannXi Set.univ s ≠ 0 := by
      intro he
      exact hs (by rw [hfac, he, mul_zero])
    rw [hfac, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (exp_ne_zero _))
      (norm_ne_zero_iff.mpr hp), norm_exp, Real.log_exp, log_norm_xi_canonicalProduct hs]
  have h0 := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
    (z := 0) hfac (fun p => (riemannXiDivisorZeroValue_ne_zero p).symm)
  have hc : P.coeff 1 = logDeriv riemannXi 0 := by
    have heval : P.derivative.eval 0 = P.coeff 1 := by
      rw [P.eq_X_add_C_of_degree_le_one hdeg]
      simp
    simpa [zero_sub, div_neg, heval] using h0.symm
  have hpoly : (P.eval (z + 1)).re - (P.eval z).re = (logDeriv riemannXi 0).re := by
    rw [P.eq_X_add_C_of_degree_le_one hdeg]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    simp only [add_re, mul_re, add_im, one_re, one_im]
    rw [← hc]
    ring
  have hsum := (summable_log_norm_xi_weierstrass (z + 1)).tsum_sub
    (summable_log_norm_xi_weierstrass z)
  simp_rw [xi_factor_log_step hz hz1] at hsum
  rw [(summable_xi_log_distance_step hz hz1).tsum_add
    summable_re_xi_divisor_reciprocal] at hsum
  rw [hlog _ hz1, hlog _ hz]
  have hconst := re_logDeriv_riemannXi_zero_eq_neg_tsum_reciprocal
  linarith

end

end PrimeFactorUnimodality
