import PrimeFactorUnimodality.Mathlib.NumberTheory.Chebyshev.PsiBounds

/-! # Elementary psi cutoff interfaces -/

set_option autoImplicit false

open Real Chebyshev

example {x r : ℝ} (hx : 1 ≤ x) (hr : log x / sqrt x ≤ r) :
    ψ x ≤ (log 4 + 2 * r) * x := psi_le_mul_of_log_div_sqrt_le hx hr

example {a x L r : ℝ} (ha : exp 2 ≤ a) (hax : a ≤ x)
    (hr : 0 < r) (hra : r ^ 2 ≤ a) (hL : 0 ≤ L) (hlog : log a ≤ L) :
    ψ x ≤ (log 4 + 2 * (L / r)) * x :=
  psi_le_mul_of_sqrt_cutoff ha hax hr hra hL hlog

example {a L r : ℝ} (ha : exp 2 ≤ a)
    (hr : 0 < r) (hra : r ^ 2 ≤ a) (hL : 0 ≤ L) (hlog : log a ≤ L) :
    ψ a ≤ (log 4 + 2 * (L / r)) * a :=
  psi_le_mul_of_sqrt_cutoff ha le_rfl hr hra hL hlog
