import PrimeFactorUnimodality.Helpers.Analytic.KadiriOuterPairs
import PrimeFactorUnimodality.Helpers.Analytic.XiHeightTail

/-! # The actual outer-divisor sum bounded by a convergent height tail

Apply the proved pair bound, preserving every xi multiplicity, then enlarge
the outer subset to the paper's full absolute-height tail. The factor `1/2` comes
from the exact same-height pairing identity. The separation hypothesis and
the numerical tail estimate are distinct remaining inputs, not conclusions
of summability or assumptions about RH.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real
open scoped ComplexConjugate

variable {θ η κ δ σ₀ σ z H : ℝ}
  (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hκ : 0 ≤ κ)
  (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hδ : 1 / 2 ≤ δ)
  (hz : z ≤ (σ - 1) / η) (hH : 0 < H)
  (hgap : 0 ≤ 2 * σ₀ - 1 - κ * (1 + 2 * δ))
  (hcut : κ * (1 + 2 * δ) + 1 - σ₀ ≤
    (2 * σ₀ - 1 - κ * (1 + 2 * δ)) * H ^ 2)

include hθ hη hκ hσ₀ hσ hδ hz hH hgap hcut

/-- Quantitative reduction of the actual outer-zero series to a height tail. -/
theorem kadiriWeight_outer_zero_sum_lower_bound (t : ℝ)
    (hfar : ∀ p : RiemannXiDivisorZeroIndex,
      ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue p) →
        |t| + H ≤ |(riemannXiDivisorZeroValue p).im|) :
    -(kadiriOuterError θ η κ σ₀ z / 2) * xiHeightTail t H ≤
      ∑' p : {p : RiemannXiDivisorZeroIndex //
        ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue p)},
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (t : ℂ) * I) - riemannXiDivisorZeroValue p.1) := by
  let P (ρ : ℂ) := ¬ kadiriCentralStrip σ ρ
  let G (ρ : ℂ) := smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η)
    κ δ (((σ : ℂ) + (t : ℂ) * I) - ρ)
  have hs : Summable (fun p : RiemannXiDivisorZeroIndex => G (riemannXiDivisorZeroValue p)) :=
    summable_kadiriWeight_zero_difference hθ hη κ δ ((σ : ℂ) + (t : ℂ) * I)
  have href : Summable (fun p : RiemannXiDivisorZeroIndex =>
      G (1 - conj (riemannXiDivisorZeroValue p))) :=
    (hs.comp_injective riemannXiDivisorSameHeightReflection.injective).congr
      (fun p => congrArg G (riemannXiDivisorZeroValue_sameHeightReflection p))
  have hpair := (hs.add href).subtype (fun p => P (riemannXiDivisorZeroValue p))
  have hsep (p : RiemannXiDivisorZeroIndex) (hp : P (riemannXiDivisorZeroValue p)) :
      H ^ 2 ≤ (t - (riemannXiDivisorZeroValue p).im) ^ 2 :=
    sq_le_sub_sq_of_abs_cutoff hH.le (hfar p hp)
  have hmajor := (summable_xi_height_inv_sq hH t hsep).mul_left
    (-kadiriOuterError θ η κ σ₀ z)
  have hb := Summable.tsum_le_tsum
    (fun p : {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)} => show
      -kadiriOuterError θ η κ σ₀ z * (1 / (t - (riemannXiDivisorZeroValue p.1).im) ^ 2) ≤
        G (riemannXiDivisorZeroValue p.1) + G (1 - conj (riemannXiDivisorZeroValue p.1)) from by
    obtain ⟨hβ₀, hβ₁⟩ := riemannXi_zero_mem_critical_strip
      (riemannXiDivisorZeroValue_eq_zero p.1)
    simpa only [mul_one_div] using kadiriWeight_outer_zero_pair_lower_bound
      hθ hη hκ hσ₀ hσ hδ hz hH hgap hcut hβ₀ hβ₁ p.2 t (hsep p.1 p.2)) hmajor hpair
  rw [tsum_mul_left] at hb
  have ht := tsum_xi_height_inv_sq_le hH t hfar
  have hm := mul_le_mul_of_nonpos_left ht
    (neg_nonpos.mpr (kadiriOuterError_nonneg hθ hη hκ hσ₀ (z := z)))
  change _ ≤ ∑' p : {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)},
    G (riemannXiDivisorZeroValue p.1)
  rw [tsum_xi_divisor_subtype_eq_half_pair P
    (fun w => not_congr (kadiriCentralStrip_reflection σ w)) hs]
  linarith only [hm, hb]

/-- Nonnegative trigonometric coefficients preserve the uniform outer-tail bound. -/
theorem kadiriWeight_weighted_outer_zero_sum_lower_bound {ι : Type*}
    (S : Finset ι) (a k : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) (t : ℝ)
    (hfar : ∀ i ∈ S, ∀ p : RiemannXiDivisorZeroIndex,
      ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue p) →
        |k i * t| + H ≤ |(riemannXiDivisorZeroValue p).im|) :
    -(kadiriOuterError θ η κ σ₀ z / 2) * (∑ i ∈ S, a i * xiHeightTail (k i * t) H) ≤
      ∑ i ∈ S, a i * ∑' p : {p : RiemannXiDivisorZeroIndex //
        ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue p)},
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (k i * t : ℝ) * I) - riemannXiDivisorZeroValue p.1) := by
  calc
    _ = ∑ i ∈ S, a i * (-(kadiriOuterError θ η κ σ₀ z / 2) *
        xiHeightTail (k i * t) H) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
      (kadiriWeight_outer_zero_sum_lower_bound hθ hη hκ hσ₀ hσ hδ hz hH hgap hcut
        (k i * t) (hfar i hi)) (ha i hi))

end

end PrimeFactorUnimodality
