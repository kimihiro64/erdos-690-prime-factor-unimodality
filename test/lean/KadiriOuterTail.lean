import PrimeFactorUnimodality.Helpers.Analytic.KadiriTailMaster

/-! # Outer-strip comparison and actual height-tail regressions

Check a full continuum of negative-numerator rational pairs at both height
signs, cutoff equality, bounded-strip domination, and the actual weighted
outer-divisor sum. The simple rational parameters below are regression
examples, not the numerical parameters for the final zero-free constant.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Real

example {σ β y : ℝ} (hσ : (99 : ℝ) / 100 ≤ σ) (hσβ : σ ≤ β) (hβ : β ≤ 1)
    (hy : (10 : ℝ) ^ 2 ≤ y ^ 2) :
    0 ≤ Real.stechkinPair σ β y - (2 / 5) * Real.stechkinPair (σ + 3 / 5) β y := by
  exact Real.stechkinPair_outer_sub_nonneg_of_cutoff (by norm_num : (1 : ℝ) / 2 < 99 / 100)
    hσ hσβ hβ (by norm_num) (by norm_num) (by norm_num) hy (by norm_num) (by norm_num)

example {σ β : ℝ} (hσ : (99 : ℝ) / 100 ≤ σ) (hσβ : σ ≤ β) (hβ : β ≤ 1) :
    0 ≤ Real.stechkinPair σ β (-10) - (2 / 5) * Real.stechkinPair (σ + 3 / 5) β (-10) := by
  exact Real.stechkinPair_outer_sub_nonneg_of_cutoff (by norm_num : (1 : ℝ) / 2 < 99 / 100)
    hσ hσβ hβ (by norm_num) (by norm_num) (H := 10) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example (t : ℝ) : (3 : ℝ) ^ 2 ≤ (t - (|t| + 3)) ^ 2 :=
  Real.sq_le_sub_sq_of_abs_cutoff (by norm_num)
    (by rw [abs_of_nonneg (by positivity : 0 ≤ |t| + 3)])

example (z : ℂ) (hre : |z.re| ≤ 1) (him : 1 ≤ z.im ^ 2) :
    1 / z.im ^ 2 ≤ 2 * ‖z‖⁻¹ ^ 2 := by
  have h := Complex.inv_im_sq_le_mul_inv_norm_sq (H := 1) zero_lt_one hre (by simpa using him)
  norm_num at h
  simpa only [one_div, inv_pow] using h

example {H : ℝ} (hH : 0 < H) :
    Summable (fun p : {p : RiemannXiDivisorZeroIndex //
      |(riemannXiDivisorZeroValue p).im| ≥ H} => 1 / (riemannXiDivisorZeroValue p.1).im ^ 2) := by
  have h := summable_xiHeightTail hH 0
  rw [abs_zero, zero_add] at h
  simpa only [zero_sub, neg_sq] using h

example (t H : ℝ) (ht : 0 ≤ t) :
    xiHeightTail t H = ∑' p : {p : RiemannXiDivisorZeroIndex //
      t + H ≤ |(riemannXiDivisorZeroValue p).im|},
      1 / (t - (riemannXiDivisorZeroValue p.1).im) ^ 2 := by
  unfold xiHeightTail
  rw [abs_of_nonneg ht]

example {θ η κ δ σ₀ σ z H : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hκ : 0 ≤ κ)
    (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hδ : 1 / 2 ≤ δ)
    (hz : z ≤ (σ - 1) / η) (hH : 0 < H)
    (hgap : 0 ≤ 2 * σ₀ - 1 - κ * (1 + 2 * δ))
    (hcut : κ * (1 + 2 * δ) + 1 - σ₀ ≤
      (2 * σ₀ - 1 - κ * (1 + 2 * δ)) * H ^ 2)
    (t : ℝ) (hfar : ∀ p : RiemannXiDivisorZeroIndex,
      ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue p) →
        |t| + H ≤ |(riemannXiDivisorZeroValue p).im|) :
    -(kadiriOuterError θ η κ σ₀ z / 2) * xiHeightTail t H ≤
      ∑' p : {p : RiemannXiDivisorZeroIndex //
        ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue p)},
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (t : ℂ) * I) - riemannXiDivisorZeroValue p.1) :=
  kadiriWeight_outer_zero_sum_lower_bound hθ hη hκ hσ₀ hσ hδ hz hH hgap hcut t hfar

end

end PrimeFactorUnimodality.Tests
