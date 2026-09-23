import PrimeFactorUnimodality.Helpers.Analytic.BacklundCircleBounds
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaLogIntegral

/-! # The actual horizontal log integral and its complete upper bound

This is the horizontal integral in Trudgian, arXiv:0903.1885, Lemmas 2.4
and 2.8. The proof uses the existing Euler continuation bound rather than
the paper's sharper convexity constants. Its finite segment includes
zeros; its infinite tail is absolutely integrable and bounded explicitly.
The complementary lower bound and the counting-error identity remain
separate analytic obligations, not hypotheses silently discharged here.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- The real horizontal logarithmic integral starting at the critical line. -/
def turingHorizontalIntegral (T : ℝ) : ℝ :=
  ∫ x in Ioi (1 / 2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + T * I)‖

/-- The complete horizontal integral exists absolutely at every nonzero height. -/
theorem integrableOn_turingHorizontalLog {T : ℝ} (hT : T ≠ 0) :
    IntegrableOn (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + T * I)‖)
      (Ioi (1 / 2 : ℝ)) := by
  have hfinite := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (1 / 2 : ℝ) ≤ 2)).mp
      (intervalIntegrable_log_norm_riemannZeta_horizontal hT (1 / 2) 2)
  have htail := integrableOn_log_norm_riemannZeta_horizontal_Ioi (by norm_num : (1 : ℝ) < 2) T
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (1 / 2 : ℝ) ≤ 2)]
  exact hfinite.union htail

/-- Any splitting point to the right of one gives the same complete horizontal integral. -/
theorem turingHorizontalIntegral_eq_split {T c : ℝ} (hT : T ≠ 0) (hc : 1 < c) :
    turingHorizontalIntegral T =
      (∫ x in (1 / 2 : ℝ)..c, Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) +
        ∫ x in Ioi c, Real.log ‖riemannZeta ((x : ℂ) + T * I)‖ := by
  exact (intervalIntegral.integral_interval_add_Ioi'
    (intervalIntegrable_log_norm_riemannZeta_horizontal hT (1 / 2) c)
    (integrableOn_log_norm_riemannZeta_horizontal_Ioi hc T)).symm

/-- Euler's existing continuation gives a uniform linear bound right of the critical line. -/
theorem norm_riemannZeta_horizontal_le_five_height {x T : ℝ}
    (hT : 1 ≤ |T|) (hx : 1 / 2 ≤ x) :
    ‖riemannZeta ((x : ℂ) + T * I)‖ ≤ 5 * |T| := by
  let s : ℂ := (x : ℂ) + T * I
  have hre : s.re = x := by simp [s]
  have him : s.im = T := by simp [s]
  have hx0 : 0 < x := by linarith
  have hs : 0 < s.re := by rwa [hre]
  have hn1 : 1 ≤ ‖s - 1‖ := by
    exact hT.trans (by simpa [him] using abs_im_le_norm (s - 1))
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hn1
  have hn : ‖s‖ ≤ x + |T| := by
    simpa only [hre, him, abs_of_pos hx0] using norm_le_abs_re_add_abs_im s
  have hratio : ‖s‖ / s.re ≤ 1 + 2 * |T| := by
    rw [hre, div_le_iff₀ hx0]
    nlinarith [mul_nonneg (abs_nonneg T) (sub_nonneg.mpr hx)]
  have hinv : 1 / ‖s - 1‖ ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn1
  have h := norm_riemannZeta_le_euler_one hs hs1
  change ‖riemannZeta s‖ ≤ 5 * |T|
  linarith

/-- The totalized real logarithm preserves the bound also at an actual zeta zero. -/
theorem log_norm_riemannZeta_horizontal_le {x T : ℝ}
    (hT : 1 ≤ |T|) (hx : 1 / 2 ≤ x) :
    Real.log ‖riemannZeta ((x : ℂ) + T * I)‖ ≤ Real.log (5 * |T|) := by
  by_cases hz : riemannZeta ((x : ℂ) + T * I) = 0
  · simp only [hz, norm_zero, Real.log_zero]
    exact Real.log_nonneg (by linarith)
  · exact Real.log_le_log (norm_pos_iff.mpr hz) (norm_riemannZeta_horizontal_le_five_height hT hx)

/-- The complete tail after two has absolute integral at most one, at every height. -/
theorem abs_integral_turingHorizontalLog_tail_two_le_one (T : ℝ) :
    |∫ x in Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + T * I)‖| ≤ 1 := by
  have hz : ‖riemannZeta (2 : ℂ)‖ ≤ 2 := by
    convert norm_riemannZeta_real_le_pole_add_one (by norm_num : (1 : ℝ) < 2) using 1
    norm_num
  have hp : 0 < ‖riemannZeta (2 : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by norm_num))
  apply (abs_integral_log_norm_riemannZeta_horizontal_Ioi_le
    (by norm_num : (1 : ℝ) < 2) T).trans
  exact (div_le_one (Real.log_pos (by norm_num))).mpr (Real.log_le_log hp hz)

/-- The complete horizontal integral has an explicit bound for both signs of the height. -/
theorem turingHorizontalIntegral_le {T : ℝ} (hT : 1 ≤ |T|) :
    turingHorizontalIntegral T ≤ (3 / 2 : ℝ) * Real.log (5 * |T|) + 1 := by
  have hT0 : T ≠ 0 := by intro he; norm_num [he] at hT
  have hi := intervalIntegral.integral_mono_on (by norm_num : (1 / 2 : ℝ) ≤ 2)
    (intervalIntegrable_log_norm_riemannZeta_horizontal hT0 (1 / 2) 2)
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => Real.log (5 * |T|)) volume (1 / 2) 2)
    (fun x hx => log_norm_riemannZeta_horizontal_le hT hx.1)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  rw [turingHorizontalIntegral_eq_split hT0 (by norm_num : (1 : ℝ) < 2)]
  have ht := (abs_le.mp (abs_integral_turingHorizontalLog_tail_two_le_one T)).2
  linarith

end

end PrimeFactorUnimodality
