import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

theorem theta_upper_of_psi_relative_error
    {x ε : Real}
    (hpsi : |Chebyshev.psi x - x| ≤ ε * x) :
    Chebyshev.theta x ≤ (1 + ε) * x := by
  have hupper : Chebyshev.psi x ≤ (1 + ε) * x := by
    have habs := (abs_le.mp hpsi).2
    linarith
  exact (Chebyshev.theta_le_psi x).trans hupper

/-! The lower half of the standard `psi`-to-`theta` argument.  The analytic
input is deliberately a relative error for `psi`; the only additional input
is a uniform upper bound for `psi` at the three prime-power roots. -/
theorem theta_lower_of_psi_relative_error
    {b x ε c : Real} (hx : Real.exp b ≤ x)
    (hpsi : |Chebyshev.psi x - x| ≤ ε * x)
    (hroot : ∀ y : Real, 0 ≤ y → Chebyshev.psi y ≤ c * y)
    (hc : 0 ≤ c) :
    (1 - ε - c * (Real.exp (-b / 2) + Real.exp (-2 * b / 3) +
      Real.exp (-4 * b / 5))) * x ≤ Chebyshev.theta x := by
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos b) hx
  have hhalf := hroot (x ^ (1 / 2 : Real)) (by positivity)
  have hthird := hroot (x ^ (1 / 3 : Real)) (by positivity)
  have hfifth := hroot (x ^ (1 / 5 : Real)) (by positivity)
  have hpsi_lower : (1 - ε) * x ≤ Chebyshev.psi x := by
    have habs := (abs_le.mp hpsi).1
    linarith
  have hprimepowers :=
    Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have htheta_upper :
      Chebyshev.psi x ≤ Chebyshev.theta x +
        Chebyshev.psi (x ^ (2 : Real)⁻¹) +
        Chebyshev.psi (x ^ (3 : Real)⁻¹) +
        Chebyshev.psi (x ^ (5 : Real)⁻¹) := by
    linarith
  have hlog_x : b ≤ Real.log x := by
    rw [← Real.log_exp b]
    exact Real.log_le_log (Real.exp_pos b) hx
  have hhalf_scale : x ^ (1 / 2 : Real) ≤ x * Real.exp (-b / 2) := by
    rw [← Real.log_le_log_iff (by positivity) (mul_pos hx_pos (Real.exp_pos _))]
    rw [Real.log_rpow hx_pos, Real.log_mul hx_pos.ne' (Real.exp_pos _).ne',
      Real.log_exp]
    nlinarith
  have hthird_scale : x ^ (1 / 3 : Real) ≤ x * Real.exp (-2 * b / 3) := by
    rw [← Real.log_le_log_iff (by positivity) (mul_pos hx_pos (Real.exp_pos _))]
    rw [Real.log_rpow hx_pos, Real.log_mul hx_pos.ne' (Real.exp_pos _).ne',
      Real.log_exp]
    nlinarith
  have hfifth_scale : x ^ (1 / 5 : Real) ≤ x * Real.exp (-4 * b / 5) := by
    rw [← Real.log_le_log_iff (by positivity) (mul_pos hx_pos (Real.exp_pos _))]
    rw [Real.log_rpow hx_pos, Real.log_mul hx_pos.ne' (Real.exp_pos _).ne',
      Real.log_exp]
    nlinarith
  have hroot_sum :
      Chebyshev.psi (x ^ (2 : Real)⁻¹) +
        Chebyshev.psi (x ^ (3 : Real)⁻¹) +
        Chebyshev.psi (x ^ (5 : Real)⁻¹) ≤
      c * x * (Real.exp (-b / 2) + Real.exp (-2 * b / 3) +
        Real.exp (-4 * b / 5)) := by
    have hhalf' : Chebyshev.psi (x ^ (2 : Real)⁻¹) ≤
        c * (x ^ (1 / 2 : Real)) := by simpa [one_div] using hhalf
    have hthird' : Chebyshev.psi (x ^ (3 : Real)⁻¹) ≤
        c * (x ^ (1 / 3 : Real)) := by simpa [one_div] using hthird
    have hfifth' : Chebyshev.psi (x ^ (5 : Real)⁻¹) ≤
        c * (x ^ (1 / 5 : Real)) := by simpa [one_div] using hfifth
    nlinarith [mul_le_mul_of_nonneg_left hhalf_scale hc,
      mul_le_mul_of_nonneg_left hthird_scale hc,
      mul_le_mul_of_nonneg_left hfifth_scale hc]
  linarith

end

end PrimeFactorUnimodality
