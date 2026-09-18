import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Primorial

set_option autoImplicit false

/-! # Logarithmic bounds for primorials -/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev

/-- The logarithm of a natural primorial is Chebyshev's theta function at the
same natural cutoff. -/
theorem log_primorial_eq_theta (q : Nat) :
    Real.log (primorial q) = Chebyshev.theta q := by
  rw [Chebyshev.theta_eq_log_primorial]
  norm_num

/-- Mathlib's elementary upper theta bound, exposed directly as a primorial
bound. -/
theorem log_primorial_le_log_four_mul (q : Nat) :
    Real.log (primorial q) ≤ Real.log 4 * q := by
  rw [log_primorial_eq_theta]
  exact Chebyshev.theta_le_log4_mul_x (by positivity)

/-- Mathlib's elementary lower theta bound, exposed directly as a primorial
bound. -/
theorem chebyshev_lower_le_log_primorial (q : Nat) :
    (q : Real) * Real.log 2 - Real.log (q + 1) -
        2 * Real.sqrt q * Real.log q ≤ Real.log (primorial q) := by
  rw [log_primorial_eq_theta]
  exact Chebyshev.theta_ge q

/-- Splitting off a fixed positive natural multiplier from a primorial inside
the real logarithm. -/
theorem log_mul_primorial (c q : Nat) (hc : 0 < c) :
    Real.log (c * primorial q) = Real.log c + Real.log (primorial q) := by
  rw [Real.log_mul]
  · exact_mod_cast hc.ne'
  · exact_mod_cast (primorial_ne_zero q)

theorem log_eight_mul_primorial_le (q : Nat) :
    Real.log (8 * primorial q) ≤ Real.log 8 + Real.log 4 * q := by
  calc
    Real.log (8 * primorial q) =
        Real.log 8 + Real.log (primorial q) :=
      log_mul_primorial 8 q (by omega)
    _ ≤ Real.log 8 + Real.log 4 * q :=
      add_le_add_right (log_primorial_le_log_four_mul q) _

end

end PrimeFactorUnimodality
