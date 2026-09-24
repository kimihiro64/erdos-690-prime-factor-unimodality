import PrimeFactorUnimodality.Helpers.Analytic.PlattContourIntegrand

set_option autoImplicit false

/-! # A shared polynomial-Gaussian majorant for bounded contour edges

Only the Gamma-factor bound differs between leftward and rightward shifts.
This estimate handles the remaining Gaussian, Fourier phase and polynomial
uniformly on any bounded vertical displacement.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- A fixed coefficient once the strip width and Gamma bound are supplied. -/
def plattContourEdgeConstant (k : ℕ) (a B t₀ h u : ℝ) : ℝ :=
  (2 * Real.pi) ^ k * B * (1 + a) ^ k *
    Real.exp (a ^ 2 / (2 * h ^ 2) + 2 * Real.pi * |u| * a + Real.pi * t₀ / 4)

/-- A uniform Gamma bound on an edge leaves a decaying polynomial-Gaussian majorant. -/
theorem norm_plattContourIntegrand_edge_le (k : ℕ) (t₀ u : ℝ)
    {h a B v w : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (hv : 1 ≤ |v|)
    (hv' : Real.pi * h ^ 2 ≤ |v|) (hwabs : |w| ≤ a)
    (hg : ‖Complex.Gamma (((1 / 4 - w / 2 : ℝ) : ℂ) +
      (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ B) :
    ‖plattContourIntegrand k t₀ h u ((v : ℂ) + (w : ℂ) * Complex.I)‖ ≤
      plattContourEdgeConstant k a B t₀ h u *
        (|v| ^ k * Real.exp (-(1 / (4 * h ^ 2)) * |v| ^ 2)) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hg
  have hp : ‖(w : ℂ) - (v : ℂ) * Complex.I‖ ≤ (1 + a) * |v| := by
    calc
      _ ≤ |w| + |v| := by
        simpa using norm_sub_le (w : ℂ) ((v : ℂ) * Complex.I)
      _ ≤ a + |v| := by linarith
      _ ≤ _ := by nlinarith
  have hsq : w ^ 2 ≤ (a) ^ 2 := by
    nlinarith [sq_abs w, mul_self_le_mul_self (abs_nonneg w) hwabs]
  have hprod : 2 * Real.pi * u * w ≤ 2 * Real.pi * |u| * a := by
    have h : u * w ≤ |u| * a := (le_abs_self (u * w)).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hwabs (abs_nonneg u))
    have hc := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * Real.pi)
    nlinarith
  have hvlin : Real.pi * v / 4 ≤ v ^ 2 / (4 * h ^ 2) := by
    calc
      _ ≤ Real.pi * |v| / 4 := by gcongr; exact le_abs_self v
      _ ≤ _ := by
        apply (le_div_iff₀ (by positivity : 0 < 4 * h ^ 2)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hv' (abs_nonneg v), sq_abs v]
  have hsplit : v ^ 2 / (2 * h ^ 2) = v ^ 2 / (4 * h ^ 2) + v ^ 2 / (4 * h ^ 2) := by
    ring
  have hexp : (w ^ 2 / (2 * h ^ 2) + 2 * Real.pi * u * w) +
      (Real.pi * (v + t₀) / 4 - v ^ 2 / (2 * h ^ 2)) ≤
        ((a) ^ 2 / (2 * h ^ 2) +
          2 * Real.pi * |u| * a + Real.pi * t₀ / 4) +
            (-(1 / (4 * h ^ 2)) * |v| ^ 2) := by
    have hd := div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ 2 * h ^ 2)
    rw [sq_abs]
    have he : -(1 / (4 * h ^ 2)) * v ^ 2 = -(v ^ 2 / (4 * h ^ 2)) := by ring
    rw [he, hsplit]
    nlinarith
  rw [norm_plattContourIntegrand_on_line]
  calc
    _ = (2 * Real.pi) ^ k *
        ‖Complex.Gamma (((1 / 4 - w / 2 : ℝ) : ℂ) +
          (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I)‖ *
        ‖(w : ℂ) - (v : ℂ) * Complex.I‖ ^ k *
        Real.exp ((w ^ 2 / (2 * h ^ 2) + 2 * Real.pi * u * w) +
          (Real.pi * (v + t₀) / 4 - v ^ 2 / (2 * h ^ 2))) := by
      rw [Real.exp_add (w ^ 2 / (2 * h ^ 2) + 2 * Real.pi * u * w)
        (Real.pi * (v + t₀) / 4 - v ^ 2 / (2 * h ^ 2))]
      ring
    _ ≤ (2 * Real.pi) ^ k *
        B *
        ((1 + a) * |v|) ^ k *
        Real.exp (((a) ^ 2 / (2 * h ^ 2) +
          2 * Real.pi * |u| * a + Real.pi * t₀ / 4) +
            (-(1 / (4 * h ^ 2)) * |v| ^ 2)) := by
      gcongr
    _ = _ := by
      unfold plattContourEdgeConstant
      simp only [Real.exp_add, mul_pow]
      ring

end

end PrimeFactorUnimodality
