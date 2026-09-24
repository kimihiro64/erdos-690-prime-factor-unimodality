import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaWindow

set_option autoImplicit false

/-! # Vanishing connecting edges for the zeta contour

Euler's continuation gives linear zeta growth uniformly across the strip.
The pi phase has norm at most one there. Multiplying the existing Gamma
edge bound therefore costs only one polynomial order, still killed by the
Gaussian at both ends of the contour.
-/

open Filter Set
open scoped Topology

namespace PrimeFactorUnimodality

/-- Uniform zeta growth on each sufficiently distant connecting edge. -/
theorem norm_riemannZeta_plattArgument_edge_le (m : ℕ) (t₀ : ℝ) {v w : ℝ}
    (hv : 1 ≤ |v|) (hvt : |t₀| + 1 ≤ |v|) (hw : w ∈ Icc (-plattRightShift m) 0) :
    ‖riemannZeta (plattZetaArgument t₀ ((v : ℂ) + (w : ℂ) * Complex.I))‖ ≤
      (4 * (m : ℝ) + 6 + 2 * |t₀|) * |v| := by
  let s := plattZetaArgument t₀ ((v : ℂ) + (w : ℂ) * Complex.I)
  have hre : s.re = 1 / 2 - w := by simp [s]
  have him : s.im = v + t₀ := by simp [s, plattZetaArgument]
  have hσ : 1 / 2 ≤ s.re ∧ s.re ≤ 2 * (m : ℝ) + 1 := by
    dsimp [plattRightShift] at hw
    rw [hre]
    constructor <;> linarith [hw.1, hw.2]
  have ht : |v| ≤ |v + t₀| + |t₀| := by
    simpa only [add_sub_cancel_right, Real.norm_eq_abs] using norm_sub_le (v + t₀) t₀
  have him1 : 1 ≤ |s.im| := by rw [him]; linarith
  have hden : 1 ≤ ‖s - 1‖ := by
    have hn := Complex.abs_im_le_norm (s - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at hn
    exact him1.trans hn
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at him1
  have hnorm : ‖s‖ ≤ 2 * (m : ℝ) + 1 + |v| + |t₀| := by
    have hn := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg (by linarith [hσ.1] : 0 ≤ s.re), him] at hn
    have ha : |v + t₀| ≤ |v| + |t₀| := by
      simpa only [Real.norm_eq_abs] using norm_add_le v t₀
    linarith [hσ.2]
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
  have hquot := div_le_div_of_nonneg_left (norm_nonneg s)
    (by norm_num : (0 : ℝ) < 1 / 2) hσ.1
  have hz := norm_riemannZeta_le_euler_one (by linarith [hσ.1] : 0 < s.re) hs1
  norm_num at hinv hquot hz
  change ‖riemannZeta s‖ ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hv
    (by positivity : 0 ≤ 4 * (m : ℝ) + 4 + 2 * |t₀|)]

/-- The complete zeta integrand retains Gaussian edge decay, with one extra polynomial order. -/
theorem norm_plattZetaContourIntegrand_right_edge_le (m k : ℕ) (t₀ x : ℝ)
    {h v w : ℝ} (hh : 0 < h) (hv : 1 ≤ |v|) (hv' : Real.pi * h ^ 2 ≤ |v|)
    (hvt : |t₀| + 1 ≤ |v|) (hw : w ∈ Icc (-plattRightShift m) 0) :
    ‖plattZetaContourIntegrand k t₀ h x ((v : ℂ) + (w : ℂ) * Complex.I)‖ ≤
      (plattRightEdgeConstant m k t₀ h x * (4 * (m : ℝ) + 6 + 2 * |t₀|)) *
        (|v| ^ (k + 1) * Real.exp (-(1 / (4 * h ^ 2)) * |v| ^ 2)) := by
  have hp1 : 1 ≤ Real.sqrt Real.pi := by
    simpa using Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
  have hp : ‖plattPiPhase t₀ ((v : ℂ) + (w : ℂ) * Complex.I)‖ ≤ 1 := by
    rw [norm_plattPiPhase]
    simpa using Real.rpow_le_one_of_one_le_of_nonpos hp1 hw.2
  have hg := norm_plattContourIntegrand_right_edge_le m k t₀ x hh hv hv' hw
  have hz := norm_riemannZeta_plattArgument_edge_le m t₀ hv hvt hw
  rw [plattZetaContourIntegrand, norm_mul, norm_mul]
  have hremove := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp
      (norm_nonneg (plattContourIntegrand k t₀ h x ((v : ℂ) + (w : ℂ) * Complex.I))))
    (norm_nonneg (riemannZeta (plattZetaArgument t₀ ((v : ℂ) + (w : ℂ) * Complex.I))))
  simp only [mul_one] at hremove
  exact hremove.trans ((mul_le_mul hg hz (norm_nonneg _) ((norm_nonneg _).trans hg)).trans_eq
    (by rw [pow_succ]; ring))

/-- Both connecting edges of the full zeta contour tend to zero. -/
theorem tendsto_integral_plattZetaContour_right_edge_zero (m k : ℕ) (t₀ x : ℝ)
    {h ε : ℝ} (hh : 0 < h) (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ y in (0 : ℝ)..(-plattRightShift m),
      plattZetaContourIntegrand k t₀ h x (((ε * T : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 0) := by
  apply Complex.tendsto_integral_vertical_zero_of_bound
    (B := fun T => (plattRightEdgeConstant m k t₀ h x * (4 * (m : ℝ) + 6 + 2 * |t₀|)) *
      (T ^ (k + 1) * Real.exp (-(1 / (4 * h ^ 2)) * T ^ 2)))
    (by simpa using ((Real.tendsto_pow_mul_exp_neg_mul_sq (k + 1)
      (by positivity : 0 < 1 / (4 * h ^ 2))).const_mul
        (plattRightEdgeConstant m k t₀ h x * (4 * (m : ℝ) + 6 + 2 * |t₀|))))
  filter_upwards [eventually_ge_atTop (max (max 1 (Real.pi * h ^ 2)) (|t₀| + 1))] with T hT
  intro y hy
  have hT₁ : 1 ≤ T := ((le_max_left _ _).trans (le_max_left _ _)).trans hT
  have hT₂ : Real.pi * h ^ 2 ≤ T := ((le_max_right _ _).trans (le_max_left _ _)).trans hT
  have hT₃ : |t₀| + 1 ≤ T := (le_max_right _ _).trans hT
  have habs : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_nonneg (by linarith)]
  have ha : 0 ≤ plattRightShift m := by unfold plattRightShift; positivity
  have hy' : y ∈ Icc (-plattRightShift m) 0 := by
    simpa only [uIcc_of_ge (neg_nonpos.mpr ha)] using hy
  simpa only [habs] using norm_plattZetaContourIntegrand_right_edge_le m k t₀ x hh
    (v := ε * T) (by simpa only [habs] using hT₁)
    (by simpa only [habs] using hT₂) (by simpa only [habs] using hT₃) hy'

end PrimeFactorUnimodality
