import PrimeFactorUnimodality.Helpers.Analytic.XiCriticalLine

/-! # Exact statement regressions for critical-line verification -/

namespace PrimeFactorUnimodality.Tests

open Complex Finset Set

example (t : ℝ) :
    (riemannXi (1 / 2 + (t : ℂ) * I)).im = 0 := by
  exact riemannXi_criticalLine_im t

example : Continuous xiCriticalLineValue := by
  exact continuous_xiCriticalLineValue

example (t : ℝ) :
    xiCriticalLineValue t = 0 ↔ riemannXi (1 / 2 + (t : ℂ) * I) = 0 := by
  exact xiCriticalLineValue_eq_zero_iff t

example {a b : ℝ} (hab : a < b)
    (hsign : xiCriticalLineValue a * xiCriticalLineValue b < 0) :
    ∃ t ∈ Ioo a b, riemannXi (1 / 2 + (t : ℂ) * I) = 0 := by
  exact exists_xi_criticalLine_zero_of_sign_change hab hsign

example {a b u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hsign : (u * xiCriticalLineValue a) * (v * xiCriticalLineValue b) < 0) :
    xiCriticalLineValue a * xiCriticalLineValue b < 0 := by
  exact xiCriticalLine_sign_change_of_scaled hu hv hsign

example {a b : ℝ} (hab : a < b)
    (hsign : xiCriticalLineValue a * xiCriticalLineValue b < 0) :
    ∃ p : RiemannXiDivisorZeroIndex, (riemannXiDivisorZeroValue p).re = 1 / 2 ∧
      (riemannXiDivisorZeroValue p).im ∈ Ioo a b := by
  exact exists_xi_criticalLine_index_of_sign_change hab hsign

example : (riemannXi (1 / 2 + (1000000000 : ℂ) * I)).im = 0 :=
  riemannXi_criticalLine_im 1000000000

example {a b : ℝ} (hab : a < b)
    (ha : xiCriticalLineValue a < 0) (hb : 0 < xiCriticalLineValue b) :
    ∃ t ∈ Ioo a b, riemannXi (1 / 2 + (t : ℂ) * I) = 0 :=
  exists_xi_criticalLine_zero_of_sign_change hab (mul_neg_of_neg_of_pos ha hb)

example {a b : ℝ} (hab : a < b)
    (ha : 0 < xiCriticalLineValue a) (hb : xiCriticalLineValue b < 0) :
    ∃ t ∈ Ioo a b, riemannXi (1 / 2 + (t : ℂ) * I) = 0 :=
  exists_xi_criticalLine_zero_of_sign_change hab (mul_neg_of_pos_of_neg ha hb)

example {a b u v : ℝ}
    (h : (Real.exp u * xiCriticalLineValue a) * (Real.exp v * xiCriticalLineValue b) < 0) :
    xiCriticalLineValue a * xiCriticalLineValue b < 0 :=
  xiCriticalLine_sign_change_of_scaled (Real.exp_pos _) (Real.exp_pos _) h

end PrimeFactorUnimodality.Tests
