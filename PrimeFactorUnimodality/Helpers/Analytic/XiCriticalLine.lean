import Mathlib.Topology.Order.IntermediateValue
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiStechkin

/-! # Critical-line zeros from signs of the actual xi function

Conjugation and the functional equation make xi real on the critical line.
The intermediate value theorem then supplies a genuine divisor label in
each open sign-change interval. Positive endpoint rescaling is allowed so
future numerical evaluations need not represent exponentially small xi values.
No endpoint sign is asserted in this module.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Set
open scoped ComplexConjugate

/-- The real restriction of the actual entire xi function to the critical line. -/
def xiCriticalLineValue (t : ℝ) : ℝ := (riemannXi (1 / 2 + (t : ℂ) * I)).re

/-- The functional equation and conjugation force the imaginary part to vanish. -/
theorem riemannXi_criticalLine_im (t : ℝ) :
    (riemannXi (1 / 2 + (t : ℂ) * I)).im = 0 := by
  have he : conj (1 / 2 + (t : ℂ) * I) = 1 - (1 / 2 + (t : ℂ) * I) := by
    apply Complex.ext <;> simp
    ring
  have h := riemannXi_conj (1 / 2 + (t : ℂ) * I)
  rw [he, riemannXi_one_sub] at h
  have hi := congrArg Complex.im h
  simp only [conj_im] at hi
  linarith

/-- Continuity comes from the existing entire xi function, not an approximate Hardy function. -/
theorem continuous_xiCriticalLineValue : Continuous xiCriticalLineValue := by
  exact continuous_re.comp (differentiable_riemannXi.continuous.comp (by fun_prop))

/-- A zero of the real restriction is a zero of the complex function. -/
theorem xiCriticalLineValue_eq_zero_iff (t : ℝ) :
    xiCriticalLineValue t = 0 ↔ riemannXi (1 / 2 + (t : ℂ) * I) = 0 := by
  constructor
  · intro h
    apply Complex.ext
    · exact h
    · exact riemannXi_criticalLine_im t
  · intro h
    exact congrArg Complex.re h

/-- Either direction of a strict sign change gives an interior critical-line zero. -/
theorem exists_xi_criticalLine_zero_of_sign_change {a b : ℝ} (hab : a < b)
    (hsign : xiCriticalLineValue a * xiCriticalLineValue b < 0) :
    ∃ t ∈ Ioo a b, riemannXi (1 / 2 + (t : ℂ) * I) = 0 := by
  have hc := continuous_xiCriticalLineValue.continuousOn (s := Icc a b)
  have hzero : (0 : ℝ) ∈ xiCriticalLineValue '' Ioo a b := by
    rcases mul_neg_iff.mp hsign with h | h
    · exact intermediate_value_Ioo' hab.le hc ⟨h.2, h.1⟩
    · exact intermediate_value_Ioo hab.le hc ⟨h.1, h.2⟩
  obtain ⟨t, ht, hz⟩ := hzero
  exact ⟨t, ht, (xiCriticalLineValue_eq_zero_iff t).mp hz⟩

/-- Positive normalization at the two endpoints preserves the required sign change. -/
theorem xiCriticalLine_sign_change_of_scaled {a b u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hsign : (u * xiCriticalLineValue a) * (v * xiCriticalLineValue b) < 0) :
    xiCriticalLineValue a * xiCriticalLineValue b < 0 := by
  have he : (u * xiCriticalLineValue a) * (v * xiCriticalLineValue b) =
      (u * v) * (xiCriticalLineValue a * xiCriticalLineValue b) := by ring
  rw [he] at hsign
  nlinarith only [mul_pos hu hv, hsign]

/-- The existing xi divisor contains a label for the zero produced by a sign-change interval. -/
theorem exists_xi_criticalLine_index_of_sign_change {a b : ℝ} (hab : a < b)
    (hsign : xiCriticalLineValue a * xiCriticalLineValue b < 0) :
    ∃ p : RiemannXiDivisorZeroIndex, (riemannXiDivisorZeroValue p).re = 1 / 2 ∧
      (riemannXiDivisorZeroValue p).im ∈ Ioo a b := by
  obtain ⟨t, ht, hz⟩ := exists_xi_criticalLine_zero_of_sign_change hab hsign
  obtain ⟨p, hp⟩ := exists_xi_divisor_index_of_zero hz
  refine ⟨p, ?_, ?_⟩
  · simp [hp]
  · simpa only [hp, add_im, div_ofNat_im, one_im, zero_div, mul_I_im,
      ofReal_re, zero_add] using ht

end

end PrimeFactorUnimodality
