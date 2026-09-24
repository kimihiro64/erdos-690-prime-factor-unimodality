import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.HalfIntegerNorm

set_option autoImplicit false

/-! # A polynomial majorant for the windowed Gamma integrand

At the odd shift `sigma = 2*m+1`, reflection and recurrence give the Gamma
factor bound directly. Triangle inequalities absorb the signed window height
into an even polynomial in its absolute value. This is the analytic input to
the Gaussian-moment replacement for the scalar `C` bound in Platt's Appendix A;
it does not assume the printed constant or certify a zero-sign computation.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The norm integrand defining Platt's scalar `C`, before the factor `(2*pi)^k`. -/
def plattGammaWindow (m k : Nat) (t₀ h v : Real) : Real :=
  ‖Complex.Gamma (((2 * (m : Real) + 1 : Real) : Complex) / 2 +
    (((v + t₀) / 2 : Real) : Complex) * Complex.I)‖ *
    Real.exp (Real.pi * (v + t₀) / 4 - v ^ 2 / (2 * h ^ 2)) *
    ‖((2 * (m : Real) + 3 / 2 : Real) : Complex) - (v : Complex) * Complex.I‖ ^ k

/-- A uniform signed-height estimate reducing the integral to Gaussian polynomial moments. -/
theorem plattGammaWindow_le_polynomial (m k : Nat) (hm : 1 ≤ m)
    {t₀ : Real} (ht₀ : 0 ≤ t₀) (h v : Real) :
    plattGammaWindow m k t₀ h v ≤
      Real.sqrt (2 * Real.pi) / 2 ^ m * (t₀ + |v| + 2 * (m : Real) - 1) ^ m *
        (2 * (m : Real) + 3 / 2 + |v|) ^ k * Real.exp (-v ^ 2 / (2 * h ^ 2)) := by
  have hm' : (1 : Real) ≤ m := by exact_mod_cast hm
  have height : |v + t₀| ≤ t₀ + |v| := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg ht₀, add_comm] using norm_add_le v t₀
  have leftPositive : 0 ≤ |v + t₀| + 2 * (m : Real) - 1 := by
    linarith [abs_nonneg (v + t₀)]
  have rightPositive : 0 ≤ t₀ + |v| + 2 * (m : Real) - 1 := by
    linarith [abs_nonneg v]
  have gammaBound := Complex.norm_Gamma_odd_half_mul_exp_le m (v + t₀)
  have gammaUpper :
      ‖Complex.Gamma (((2 * (m : Real) + 1 : Real) : Complex) / 2 +
        (((v + t₀) / 2 : Real) : Complex) * Complex.I)‖ *
          Real.exp (Real.pi * (v + t₀) / 4) ≤
        Real.sqrt (2 * Real.pi) / 2 ^ m * (t₀ + |v| + 2 * (m : Real) - 1) ^ m :=
    gammaBound.trans (by
      calc
        _ = Real.sqrt (2 * Real.pi) / 2 ^ m * (|v + t₀| + 2 * (m : Real) - 1) ^ m := by
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ leftPositive (by linarith) m) (by positivity))
  have realPositive : 0 ≤ 2 * (m : Real) + 3 / 2 := by positivity
  have factor :
      ‖((2 * (m : Real) + 3 / 2 : Real) : Complex) - (v : Complex) * Complex.I‖ ≤
        2 * (m : Real) + 3 / 2 + |v| := by
    calc
      _ ≤ ‖((2 * (m : Real) + 3 / 2 : Real) : Complex)‖ +
          ‖(v : Complex) * Complex.I‖ := norm_sub_le _ _
      _ = _ := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg realPositive, Complex.norm_real, Real.norm_eq_abs]
  have productBound := mul_le_mul gammaUpper
    (pow_le_pow_left₀ (norm_nonneg _) factor k) (pow_nonneg (norm_nonneg _) k)
    (mul_nonneg (by positivity) (pow_nonneg rightPositive m))
  apply (le_of_eq ?_).trans
    (mul_le_mul_of_nonneg_right productBound (Real.exp_pos _).le)
  unfold plattGammaWindow
  rw [sub_eq_add_neg, Real.exp_add]
  simp only [neg_div]
  ring

end

end PrimeFactorUnimodality
