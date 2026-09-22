import PrimeFactorUnimodality.Helpers.Analytic.SmoothedRealExplicitFormula

/-! # The compactly smoothed Stechkin master inequality

Subtracting a right-shifted explicit formula and applying trigonometric
positivity gives the master inequality of Kadiri's method. Absolute
summability justifies moving the finite polynomial sum inside the complete
xi divisor sum. The gamma terms retain their actual digamma values and
boundary integrals; no estimates or explicit-formula premises are assumed.
The source identities are equations (8) and (10) of
<https://www.cs.uleth.ca/~kadiri/articles/zeta-acta-04-09-07.pdf>.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Set

/-- The shifted real Laplace contribution, used for the pole and every zero. -/
def smoothedLaplaceDifference (f : ℝ → ℝ) (d κ δ : ℝ) (s : ℂ) : ℝ :=
  (finiteLaplace (fun u => (f u : ℂ)) d s).re -
    κ * (finiteLaplace (fun u => (f u : ℂ)) d (s + (δ : ℂ))).re

/-- The exact shifted gamma factor multiplying the endpoint value. -/
def smoothedGammaFactorDifference (κ δ : ℝ) (s : ℂ) : ℝ :=
  (-(1 / 2 : ℝ) * Real.log Real.pi + (1 / 2 : ℝ) * (digamma (s / 2 + 1)).re) -
    κ * (-(1 / 2 : ℝ) * Real.log Real.pi +
      (1 / 2 : ℝ) * (digamma ((s + (δ : ℂ)) / 2 + 1)).re)

/-- The exact shifted gamma boundary remainder. -/
def smoothedGammaRemainderDifference (h : ℝ → ℂ) (d κ δ : ℝ) (s : ℂ) : ℝ :=
  (smoothedGammaRemainder h d s).re - κ * (smoothedGammaRemainder h d (s + (δ : ℂ))).re

variable {f : ℝ → ℝ} {g h : ℝ → ℂ} {d M : ℝ}
  (hd : 0 ≤ d) (hM : 0 ≤ M)
  (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
  (hh : ContinuousOn h (Icc 0 d))
  (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt (fun u => (f u : ℂ)) (g u) u)
  (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
  (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
  (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M)

include hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound

/-- The shifted real zero contributions are absolutely summable at every complex point. -/
theorem summable_smoothedLaplaceDifference_zeros (κ δ : ℝ) (s : ℂ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      smoothedLaplaceDifference f d κ δ (s - riemannXiDivisorZeroValue p)) := by
  have hfc : ContinuousOn (fun u => (f u : ℂ)) (Icc 0 d) :=
    Complex.continuous_ofReal.comp_continuousOn hf
  have hfdc : (f d : ℂ) = 0 := by rw [hfd]; rfl
  have hsum (w : ℂ) := summable_re_xi_finiteLaplace hd hM hfc hg hh hfg hgh
    hfdc hg₀ hgd hbound (by simp) w
  apply ((hsum s).sub ((hsum (s + (δ : ℂ))).mul_left κ)).congr
  intro p
  dsimp [smoothedLaplaceDifference]
  rw [show s + (δ : ℂ) - riemannXiDivisorZeroValue p =
    (s - riemannXiDivisorZeroValue p) + (δ : ℂ) by ring]

/-- The difference of the two actual explicit formulas, including the whole zero sum. -/
theorem re_smoothedVonMangoldt_sub_shift_eq
    (htail : ∀ u, d < u → f u = 0) {κ δ : ℝ} (hδ : 0 ≤ δ)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    (smoothedVonMangoldt f s).re - κ * (smoothedVonMangoldt f (s + (δ : ℂ))).re =
      smoothedLaplaceDifference f d κ δ (s - 1) -
      (∑' p : RiemannXiDivisorZeroIndex,
        smoothedLaplaceDifference f d κ δ (s - riemannXiDivisorZeroValue p)) +
      f 0 * smoothedGammaFactorDifference κ δ s + smoothedGammaRemainderDifference h d κ δ s := by
  have hfc : ContinuousOn (fun u => (f u : ℂ)) (Icc 0 d) :=
    Complex.continuous_ofReal.comp_continuousOn hf
  have hfdc : (f d : ℂ) = 0 := by rw [hfd]; rfl
  have hsum (w : ℂ) := summable_re_xi_finiteLaplace hd hM hfc hg hh hfg hgh
    hfdc hg₀ hgd hbound (by simp) w
  have hshift (z : ℂ) : s + (δ : ℂ) - z = (s - z) + (δ : ℂ) := by ring
  have hA := re_smoothedVonMangoldt_explicitFormula hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound htail hs
  have hB := re_smoothedVonMangoldt_explicitFormula hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound htail (s := s + (δ : ℂ)) (by simp only [add_re, ofReal_re]; linarith)
  have hz := (hsum s).tsum_sub ((hsum (s + (δ : ℂ))).mul_left κ)
  rw [tsum_mul_left] at hz
  simp_rw [hshift] at hB hz
  unfold smoothedLaplaceDifference smoothedGammaFactorDifference smoothedGammaRemainderDifference
  rw [hz]
  linear_combination hA - κ * hB

/-- Kadiri's smoothed master inequality with the zero sum grouped by its actual divisor. -/
theorem smoothedStechkin_master_nonneg {ι : Type*} (S : Finset ι) (a k : ι → ℝ)
    (htail : ∀ u, d < u → f u = 0) (hf₀ : ∀ u, 0 ≤ u → 0 ≤ f u)
    {σ κ δ : ℝ} (hσ : 1 / 2 < σ) (hδ : 0 ≤ δ) (hκ : κ ≤ 1) (t : ℝ)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ S, a i * Real.cos (k i * u)) :
    0 ≤ (∑ i ∈ S, a i * smoothedLaplaceDifference f d κ δ
        (((σ : ℂ) + (k i * t : ℝ) * I) - 1)) -
      (∑' p : RiemannXiDivisorZeroIndex, ∑ i ∈ S, a i * smoothedLaplaceDifference f d κ δ
        (((σ : ℂ) + (k i * t : ℝ) * I) - riemannXiDivisorZeroValue p)) +
      f 0 * (∑ i ∈ S, a i * smoothedGammaFactorDifference κ δ
        ((σ : ℂ) + (k i * t : ℝ) * I)) +
      ∑ i ∈ S, a i * smoothedGammaRemainderDifference h d κ δ
        ((σ : ℂ) + (k i * t : ℝ) * I) := by
  have hp := sum_mul_re_shifted_smoothedVonMangoldt_nonneg S a k htail hf₀
    (σ := σ) (τ := σ + δ) (by linarith) hκ t hpoly
  have hshift (i : ι) : ((σ + δ : ℝ) : ℂ) + (k i * t : ℝ) * I =
      ((σ : ℂ) + (k i * t : ℝ) * I) + (δ : ℂ) := by push_cast; ring
  simp_rw [hshift] at hp
  have hid (i : ι) := re_smoothedVonMangoldt_sub_shift_eq hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound htail hδ (κ := κ)
    (s := (σ : ℂ) + (k i * t : ℝ) * I) (by simpa using hσ)
  simp_rw [hid] at hp
  have hz := Summable.tsum_finsetSum (s := S) (fun i _ =>
    (summable_smoothedLaplaceDifference_zeros hd hM hf hg hh hfg hgh
      hfd hg₀ hgd hbound κ δ ((σ : ℂ) + (k i * t : ℝ) * I)).mul_left (a i))
  simp_rw [tsum_mul_left] at hz
  rw [hz]
  simpa only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_left_comm] using hp

end

end PrimeFactorUnimodality
