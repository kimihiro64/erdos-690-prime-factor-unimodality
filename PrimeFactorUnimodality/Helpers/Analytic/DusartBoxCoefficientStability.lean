import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPhaseRows
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageVertical

/-! # Explicit stability of the centered low-zero coefficients

The derivative-free bound uses the averaging support and a positive lower
ordinate. It controls every point in a zero enclosure from a single center
evaluation, with no inverse power of the smoothing step.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex intervalIntegral

/-- The largest critical-line power amplitude on the averaging support. -/
def dusartBoxCoefficientAmplitude (m : ℕ) (s : ℝ) : ℝ :=
  Real.exp ((1 / 2 : ℝ) * Real.log (1 + (m + 3 : ℕ) * s))

/-- A uniform ordinate slope, including the coefficient's fixed centering phase. -/
def dusartBoxCoefficientSlope (m : ℕ) (s u L : ℝ) : ℝ :=
  dusartBoxCoefficientAmplitude m s *
    (1 / L ^ 2 + (Real.log (1 + (m + 3 : ℕ) * s) + |u|) / L)

/-- The slope is nonnegative for positive steps and positive lower ordinates. -/
theorem dusartBoxCoefficientSlope_nonneg (m : ℕ) {s L : ℝ} (hs : 0 < s)
    (u : ℝ) (hL : 0 < L) : 0 ≤ dusartBoxCoefficientSlope m s u L := by
  have hl : 0 ≤ Real.log (1 + (m + 3 : ℕ) * s) :=
    Real.log_nonneg (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hs.le))
  unfold dusartBoxCoefficientSlope dusartBoxCoefficientAmplitude
  positivity

private theorem norm_criticalLine_ge (γ : ℝ) : γ ≤ ‖(1 / 2 : ℂ) + γ * I‖ := by
  simpa using im_le_norm ((1 / 2 : ℂ) + γ * I)

/-- Averaging cannot enlarge the support amplitude divided by a lower ordinate. -/
theorem norm_dusartBoxOrdinateCoefficient_le (m : ℕ) {s L γ : ℝ}
    (hs : 0 < s) (u : ℝ) (hL : 0 < L) (hγ : L ≤ γ) :
    ‖dusartBoxOrdinateCoefficient m s u γ‖ ≤ dusartBoxCoefficientAmplitude m s / L := by
  unfold dusartBoxOrdinateCoefficient
  rw [norm_mul]
  have he : ‖exp (I * ((u * γ : ℝ) : ℂ))‖ = 1 := by simp [norm_exp, mul_re]
  rw [he, mul_one]
  simpa [dusartBoxCoefficientAmplitude] using
    norm_iteratedBoxAverageComplex_cpow_div_le_of_norm_ge hs
      (z := (1 / 2 : ℂ) + γ * I) (by norm_num) hL (hγ.trans (norm_criticalLine_ge γ)) (m + 3)

/-- A stable Lipschitz bound for the actual coefficient at any two positive ordinates. -/
theorem norm_dusartBoxOrdinateCoefficient_sub_le (m : ℕ) {s L γ δ : ℝ}
    (hs : 0 < s) (u : ℝ) (hL : 0 < L) (hγ : L ≤ γ) (hδ : L ≤ δ) :
    ‖dusartBoxOrdinateCoefficient m s u γ - dusartBoxOrdinateCoefficient m s u δ‖ ≤
      dusartBoxCoefficientSlope m s u L * |γ - δ| := by
  let z : ℂ := (1 / 2 : ℂ) + γ * I
  let w : ℂ := (1 / 2 : ℂ) + δ * I
  let F := fun q : ℂ => iteratedBoxAverageComplex s (m + 3) (fun t => (t : ℂ) ^ q / q) 1
  have hz : L ≤ ‖z‖ := hγ.trans (norm_criticalLine_ge γ)
  have hw : L ≤ ‖w‖ := hδ.trans (norm_criticalLine_ge δ)
  have hd : ‖z - w‖ = |γ - δ| := by
    have he : z - w = ((γ - δ : ℝ) : ℂ) * I := by dsimp [z, w]; push_cast; ring
    rw [he, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  have hdiff : ‖F z - F w‖ ≤ dusartBoxCoefficientAmplitude m s *
      (|γ - δ| / L ^ 2 + Real.log (1 + (m + 3 : ℕ) * s) * |γ - δ| / L) := by
    have he := norm_iteratedBoxAverageComplex_cpow_div_sub_le hs (z := z) (w := w)
      (by simp [z, w]) (by norm_num [z]) hL hz hw (m + 3)
    rw [hd] at he
    simpa [F, z, w, dusartBoxCoefficientAmplitude] using he
  have hn : ‖F w‖ ≤ dusartBoxCoefficientAmplitude m s / L := by
    simpa [F, w, dusartBoxCoefficientAmplitude] using
      norm_iteratedBoxAverageComplex_cpow_div_le_of_norm_ge hs (z := w)
        (by norm_num [w]) hL hw (m + 3)
  have hrot := norm_rotated_sub_rotated_le (u * γ) (u * δ) (F z) (F w)
  have hbound := hrot.trans (add_le_add hdiff
    (mul_le_mul_of_nonneg_right hn (abs_nonneg (u * γ - u * δ))))
  calc
    _ = ‖exp (I * ↑(u * γ)) * F z - exp (I * ↑(u * δ)) * F w‖ := by
      simp only [dusartBoxOrdinateCoefficient, F, z, w, mul_comm]
    _ ≤ _ := hbound
    _ = _ := by rw [← mul_sub, abs_mul]; unfold dusartBoxCoefficientSlope; ring

/-- A center enclosure and an ordinate radius supply the whole row's coefficient error. -/
theorem norm_dusartBoxOrdinateCoefficient_sub_center_le (m : ℕ) {s L γ δ r e : ℝ}
    (hs : 0 < s) (u : ℝ) (hL : 0 < L) (hγ : L ≤ γ) (hδ : L ≤ δ)
    (hr : |γ - δ| ≤ r) {c : ℂ} (hc : ‖dusartBoxOrdinateCoefficient m s u δ - c‖ ≤ e) :
    ‖dusartBoxOrdinateCoefficient m s u γ - c‖ ≤
      dusartBoxCoefficientSlope m s u L * r + e := by
  have hd := (norm_dusartBoxOrdinateCoefficient_sub_le m hs u hL hγ hδ).trans
    (mul_le_mul_of_nonneg_left hr (dusartBoxCoefficientSlope_nonneg m hs u hL))
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hd hc)

end

end PrimeFactorUnimodality
