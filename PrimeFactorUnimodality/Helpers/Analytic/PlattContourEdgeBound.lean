import PrimeFactorUnimodality.Helpers.Analytic.PlattContourIntegrand
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.StripBound

set_option autoImplicit false

/-! # A uniform bound on the connecting edges of the rightward contour

The Gamma argument stays in a closed positive strip. Euler's integral and
convexity bound it uniformly, and the remaining exponential is absorbed by
a Gaussian for all sufficiently large absolute real coordinates.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The height of the downward displacement corresponding to Gamma real part `m+1/2`. -/
def plattRightShift (m : ℕ) : ℝ := 2 * (m : ℝ) + 1 / 2

/-- A fixed coefficient for the uniform polynomial-Gaussian edge bound. -/
def plattRightEdgeConstant (m k : ℕ) (t₀ h u : ℝ) : ℝ :=
  (2 * Real.pi) ^ k * max (Real.Gamma (1 / 4)) (Real.Gamma ((m : ℝ) + 1 / 2)) *
    (1 + plattRightShift m) ^ k *
      Real.exp ((plattRightShift m) ^ 2 / (2 * h ^ 2) +
        2 * Real.pi * |u| * plattRightShift m + Real.pi * t₀ / 4)

/-- The full complex integrand decays uniformly across the entire connecting edge. -/
theorem norm_plattContourIntegrand_right_edge_le (m k : ℕ) (t₀ u : ℝ)
    {h : ℝ} (hh : 0 < h) {v w : ℝ} (hv : 1 ≤ |v|)
    (hv' : Real.pi * h ^ 2 ≤ |v|) (hw : w ∈ Set.Icc (-plattRightShift m) 0) :
    ‖plattContourIntegrand k t₀ h u ((v : ℂ) + (w : ℂ) * Complex.I)‖ ≤
      plattRightEdgeConstant m k t₀ h u *
        (|v| ^ k * Real.exp (-(1 / (4 * h ^ 2)) * |v| ^ 2)) := by
  have ha : 0 ≤ plattRightShift m := by unfold plattRightShift; positivity
  have hwabs : |w| ≤ plattRightShift m := by
    rw [abs_of_nonpos hw.2]
    linarith [hw.1]
  have hg := Complex.norm_Gamma_le_max_of_re_mem_Icc
    (a := 1 / 4) (b := (m : ℝ) + 1 / 2) (by norm_num) (by positivity)
    (s := ((1 / 4 - w / 2 : ℝ) : ℂ) + (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I)
    (by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Set.mem_Icc]
      dsimp [plattRightShift] at hw
      constructor <;> linarith [hw.1, hw.2])
  have hp : ‖(w : ℂ) - (v : ℂ) * Complex.I‖ ≤ (1 + plattRightShift m) * |v| := by
    calc
      _ ≤ |w| + |v| := by
        simpa using norm_sub_le (w : ℂ) ((v : ℂ) * Complex.I)
      _ ≤ plattRightShift m + |v| := by linarith
      _ ≤ _ := by nlinarith
  have hsq : w ^ 2 ≤ (plattRightShift m) ^ 2 := by
    nlinarith [sq_abs w, mul_self_le_mul_self (abs_nonneg w) hwabs]
  have hprod : 2 * Real.pi * u * w ≤ 2 * Real.pi * |u| * plattRightShift m := by
    have h : u * w ≤ |u| * plattRightShift m := (le_abs_self (u * w)).trans (by
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
        ((plattRightShift m) ^ 2 / (2 * h ^ 2) +
          2 * Real.pi * |u| * plattRightShift m + Real.pi * t₀ / 4) +
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
        max (Real.Gamma (1 / 4)) (Real.Gamma ((m : ℝ) + 1 / 2)) *
        ((1 + plattRightShift m) * |v|) ^ k *
        Real.exp (((plattRightShift m) ^ 2 / (2 * h ^ 2) +
          2 * Real.pi * |u| * plattRightShift m + Real.pi * t₀ / 4) +
            (-(1 / (4 * h ^ 2)) * |v| ^ 2)) := by
      gcongr
    _ = _ := by
      unfold plattRightEdgeConstant
      simp only [Real.exp_add, mul_pow]
      ring

end

end PrimeFactorUnimodality
