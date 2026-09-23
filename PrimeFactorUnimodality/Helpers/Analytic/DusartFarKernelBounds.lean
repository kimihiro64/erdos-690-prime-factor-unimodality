import PrimeFactorUnimodality.Helpers.Analytic.XiRosserNuWindow
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserSharpTail

/-! # Elementary Rosser kernel bounds at parameter four fifths

At root parameter at least twenty-eight, both scalar zero contributions
have a simple exponential majorant. These inequalities keep the full
sharp high-tail exponent before the smoothing coefficient is inserted.
They make no numerical zero-free-region assumption.
-/

namespace PrimeFactorUnimodality

open Real

private theorem far_density_atom_le {u v X : ℝ} (hu : u ≤ X)
    (hX : 0 ≤ X) (hv : 0 ≤ v) : (1 / (2 * π)) * (v * u) ≤ v * X := by
  have hc : 1 / (2 * π) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * π)).mpr
    linarith [pi_gt_three]
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu hv)
    (by positivity)).trans ((mul_le_mul_of_nonneg_right hc (mul_nonneg hv hX)).trans_eq
      (one_mul _))

/-- Both signs of the finite-window contribution have a single exponential majorant. -/
theorem xiRosserNuWindowBound_four_fifths_le {X : ℝ} (hX : 28 ≤ X) :
    2 * xiRosserNuWindowBound X (4 / 5) ≤ 16 * X * exp (-(5 / 4 : ℝ) * X) := by
  have hXpos : 0 < X := by linarith
  have hlog : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [pi_gt_three])
  have hfirst : (1 / (2 * π)) * (exp (-(5 / 4 : ℝ) * X) * (16 / 25) *
      ((4 / 5) * X - Real.log (2 * π))) ≤ exp (-(5 / 4 : ℝ) * X) * X := by
    convert far_density_atom_le (v := exp (-(5 / 4 : ℝ) * X))
      (u := (16 / 25) * ((4 / 5) * X - Real.log (2 * π)))
      (by linarith) hXpos.le (Real.exp_pos _).le using 1
    ring
  have he := Real.exp_le_exp.mpr
    (by linarith : -(4 / 5 : ℝ) * X - (5 / 4) * X ≤ -(5 / 4 : ℝ) * X)
  have hsecond : 2 * ((4 / 5 : ℝ) * X + 17) *
      exp (-(4 / 5 : ℝ) * X - (5 / 4) * X) ≤ 4 * X * exp (-(5 / 4 : ℝ) * X) := by
    exact (mul_le_mul_of_nonneg_left he (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
  unfold xiRosserNuWindowBound
  rw [show -X / (4 / 5 : ℝ) = -(5 / 4 : ℝ) * X by ring,
    show -(4 / 5 * X) - X / (4 / 5 : ℝ) = -(4 / 5 : ℝ) * X - (5 / 4) * X by ring]
  norm_num only [show (4 / 5 : ℝ) ^ 2 = 16 / 25 by norm_num]
  nlinarith only [hfirst, hsecond, mul_pos hXpos (Real.exp_pos (-(5 / 4 : ℝ) * X))]

/-- The complete sharp scalar tail retains its faster high-height exponential. -/
theorem xiRosserSharpTailBound_four_fifths_le {X : ℝ} (hX : 28 ≤ X) :
    xiRosserSharpTailBound X 3 (4 / 5) ≤ 16 * X * exp (-(73 / 20 : ℝ) * X) := by
  have hXpos : 0 < X := by linarith
  have hlog : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [pi_gt_three])
  have hfirst : (1 / (2 * π)) * (exp (-(73 / 20 : ℝ) * X) * (16 / 23) *
      ((4 / 5) * X + 1 / 3 - Real.log (2 * π))) ≤ exp (-(73 / 20 : ℝ) * X) * X := by
    convert far_density_atom_le (v := exp (-(73 / 20 : ℝ) * X))
      (u := (16 / 23) * ((4 / 5) * X + 1 / 3 - Real.log (2 * π)))
      (by linarith) hXpos.le (Real.exp_pos _).le using 1
    ring
  have he := Real.exp_le_exp.mpr
    (by linarith : -(89 / 20 : ℝ) * X ≤ -(73 / 20 : ℝ) * X)
  have hsecond : exp (-(89 / 20 : ℝ) * X) / (39 / 16) ≤ exp (-(73 / 20 : ℝ) * X) := by
    exact (div_le_div_of_nonneg_right he (by norm_num)).trans
      ((div_le_iff₀ (by norm_num : (0 : ℝ) < 39 / 16)).mpr
        (by nlinarith [(Real.exp_pos (-(73 / 20 : ℝ) * X))]))
  have hthird : 2 * ((4 / 5 : ℝ) * X + 17) * exp (-(89 / 20 : ℝ) * X) ≤
      4 * X * exp (-(73 / 20 : ℝ) * X) := by
    exact (mul_le_mul_of_nonneg_left he (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
  unfold xiRosserSharpTailBound
  rw [show -(3 : ℝ) * ((4 / 5) * X) - X / (4 / 5) = -(73 / 20 : ℝ) * X by ring,
    show -((3 : ℝ) + 1) * ((4 / 5) * X) - X / (4 / 5) = -(89 / 20 : ℝ) * X by ring]
  norm_num only [show (4 / 5 : ℝ) ^ 2 / (3 * (4 / 5) ^ 2 - 1) = 16 / 23 by norm_num,
    show (3 : ℝ) + 1 - 1 / (4 / 5) ^ 2 = 39 / 16 by norm_num]
  nlinarith only [hfirst, hsecond, hthird, Real.exp_pos (-(73 / 20 : ℝ) * X),
    mul_nonneg (by linarith : 0 ≤ X - 1) (Real.exp_pos (-(73 / 20 : ℝ) * X)).le]

end PrimeFactorUnimodality
