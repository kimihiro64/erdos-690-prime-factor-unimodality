import PrimeFactorUnimodality.Helpers.Analytic.RelativePsiTheta
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryChebyshevConsequences

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-! The numerical tail step used in Dusart's theta estimate. -/
theorem theta_le_one_plus_dusart_error_of_psi_upper_and_gap
    {x : Real}
    (hpsi : Chebyshev.psi x ≤ (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x ≤
      (100002841 : Real) / 100000000 * x -
        (9999 : Real) / 10000 * Real.sqrt x := by
  linarith

theorem dusart_gap_from_theta_root_lower
    {x : Real} (hx : 2 ≤ x)
    (hroot : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.theta (x ^ (1 / 2 : Real))) :
    (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hdecomp := psi_sub_theta_ge_theta_sqrt hx
  have hroot' : (9999 : Real) / 10000 * x ^ (1 / 2 : Real) ≤
      Chebyshev.theta (x ^ (1 / 2 : Real)) := by
    simpa only [Real.sqrt_eq_rpow] using hroot
  simpa only [Real.sqrt_eq_rpow] using hroot'.trans hdecomp

theorem psi_sub_theta_ge_elementary_sqrt_gap
    {x : Real} (hx : (62500000000 : Real) ≤ x) :
    (86 : Real) / 100 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hx_pos : 0 < x := by linarith
  have hroot_lower : (250000 : Real) ≤ Real.sqrt x := by
    apply (Real.le_sqrt' (by norm_num : (0 : Real) < 250000)).2
    nlinarith
  have htheta := elementary_theta_lower_from_250000 hroot_lower
  have hdecomp := psi_sub_theta_ge_theta_sqrt (by linarith : (2 : Real) ≤ x)
  have htheta' : (86 : Real) / 100 * Real.sqrt x ≤
      Chebyshev.theta (Real.sqrt x) := by
    simpa only [Real.sqrt_eq_rpow] using htheta
  have hdecomp' : Chebyshev.theta (Real.sqrt x) ≤
      Chebyshev.psi x - Chebyshev.theta x := by
    simpa only [Real.sqrt_eq_rpow] using hdecomp
  exact htheta'.trans hdecomp'

theorem dusart_theta_upper_tail_step
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_upper : x ≤ (1446257064292 : Real))
    (hpsi : Chebyshev.psi x ≤ (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x ≤ x / 36260 := by
  have hx_pos : 0 < x := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x := by
    simpa using Real.sq_sqrt (le_of_lt hx_pos)
  have hmain := theta_le_one_plus_dusart_error_of_psi_upper_and_gap hpsi hgap
  have hlinear :
      (100002841 : Real) / 100000000 * x -
          (9999 : Real) / 10000 * Real.sqrt x - x ≤ x / 36260 := by
    have hsqrt_lower : (894000 : Real) ≤ Real.sqrt x := by
      apply (Real.le_sqrt' (by norm_num : (0 : Real) < 894000)).2
      nlinarith
    have hsqrt_upper : Real.sqrt x ≤ (1202668 : Real) := by
      apply (Real.sqrt_le_iff).2
      constructor
      · norm_num
      · nlinarith
    have hxs : x ≤ (1202668 : Real) * Real.sqrt x := by
      calc
        x = Real.sqrt x * Real.sqrt x := by nlinarith [hsqrt_sq]
        _ ≤ (1202668 : Real) * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hsqrt_upper hsqrt_nonneg
    nlinarith
  linarith

end
end PrimeFactorUnimodality
