import PrimeFactorUnimodality.Helpers.Analytic.PlattContourSharedEdgeBound
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
  simpa only [plattContourEdgeConstant, plattRightEdgeConstant] using
    norm_plattContourIntegrand_edge_le k t₀ u hh ha hv hv' hwabs hg

end

end PrimeFactorUnimodality
