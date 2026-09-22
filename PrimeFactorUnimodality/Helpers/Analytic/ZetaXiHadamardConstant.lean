import PrimeFactorUnimodality.Helpers.Analytic.SmoothedXiRemainder
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiDivisorReflection
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiStechkin

/-! # Cancellation of the real Hadamard constant

Reflection of the actual xi divisor preserves multiplicities. At `s=1`,
the Hadamard expansion and the functional equation therefore identify the
real constant with the negative sum of real reciprocal zeros. Substituting
this value removes the constant at every point where xi is nonzero.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The real reciprocal-zero sum is absolutely convergent. -/
theorem summable_re_xi_divisor_reciprocal :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      (1 / riemannXiDivisorZeroValue p).re) := by
  simpa only [zero_sub, div_neg, neg_re, neg_neg] using
    (summable_re_xi_divisor_resolvent 0).neg

/-- The real Hadamard constant is exactly the negative real reciprocal-zero sum. -/
theorem re_logDeriv_riemannXi_zero_eq_neg_tsum_reciprocal :
    (logDeriv riemannXi 0).re =
      -(∑' p : RiemannXiDivisorZeroIndex, (1 / riemannXiDivisorZeroValue p).re) := by
  have h1 : riemannXi 1 ≠ 0 := by
    have h := riemannXi_one_sub 0
    norm_num [riemannXi_zero] at h
    rw [h]
    norm_num
  have hs := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ (z := 1)
    (fun p heq => h1 (heq ▸ riemannXiDivisorZeroValue_eq_zero p))
  have hreflect := riemannXiDivisorReflection.tsum_eq
    (fun p => (1 / riemannXiDivisorZeroValue p).re)
  simp only [riemannXiDivisorZeroValue_reflection] at hreflect
  have h := congrArg Complex.re (logDeriv_riemannXi_eq_zero_add_tsum_of_ne_zero h1)
  rw [add_re, re_tsum hs] at h
  simp only [add_re] at h
  rw [(summable_re_xi_divisor_resolvent 1).tsum_add
    summable_re_xi_divisor_reciprocal, hreflect] at h
  have hsym := congrArg Complex.re (logDeriv_riemannXi_one_sub 0)
  simp only [sub_zero, neg_re] at hsym
  linarith

/-- The real logarithmic derivative is the absolutely convergent resolvent sum. -/
theorem re_logDeriv_riemannXi_eq_tsum_resolvent {s : ℂ} (hs : riemannXi s ≠ 0) :
    (logDeriv riemannXi s).re =
      ∑' p : RiemannXiDivisorZeroIndex, (1 / (s - riemannXiDivisorZeroValue p)).re := by
  have hsum := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ (z := s)
    (fun p heq => hs (heq ▸ riemannXiDivisorZeroValue_eq_zero p))
  rw [logDeriv_riemannXi_eq_zero_add_tsum_of_ne_zero hs, add_re, re_tsum hsum,
    re_logDeriv_riemannXi_zero_eq_neg_tsum_reciprocal]
  simp only [add_re]
  rw [(summable_re_xi_divisor_resolvent s).tsum_add summable_re_xi_divisor_reciprocal]
  ring

end

end PrimeFactorUnimodality
