import PrimeFactorUnimodality.Helpers.Analytic.DusartSharperRootCorrection

/-! # Sharp root correction interfaces and closed boundary tests -/

set_option autoImplicit false

open Real Chebyshev PrimeFactorUnimodality

example : ψ 40000 ≤ (3 / 2 : ℝ) * 40000 := psi_le_three_halves_mul le_rfl

example : ψ 1000 ≤ 2 * 1000 := psi_le_two_mul_from_thousand le_rfl

example : ψ 3000000000 - θ 3000000000 ≤
    (8 / 5 : ℝ) * exp (log 3000000000 / 2) := psi_sub_theta_le_sharper_root le_rfl

example {x r ε : ℝ} (hx : (3000000000 : ℝ) ≤ x) (hr : 0 < r) (hrx : r ^ 2 ≤ x)
    (hpsi : |ψ x - x| / x ≤ ε) : |θ x - x| / x ≤ ε + (8 / 5) / r :=
  abs_theta_sub_div_le_sharper_root hx hr hrx hpsi
