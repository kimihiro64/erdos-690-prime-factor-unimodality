import PrimeFactorUnimodality.Helpers.Analytic.KadiriLehmanMaster

/-! # Closed tail bounds across all harmonic cases

Check zero, negative, and arbitrarily large natural harmonics. The zero
case retains the actual finite low mass, not a guessed numerical value.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Real

example {H : ℝ} (hH : 0 < H) (t : ℝ) : xiHeightTail (-t) H = xiHeightTail t H :=
  xiHeightTail_neg hH t

example {H : ℝ} (hH : 0 < H) (t : ℝ) : xiHeightTail |t| H = xiHeightTail t H :=
  xiHeightTail_abs hH t

example {H : ℝ} (hH : 0 < H) :
    xiHeightTail 0 H ≤ xiLehmanTailMajorant 0 H :=
  xiHeightTail_le_lehmanMajorant hH (fun hn => (hn rfl).elim)

example (H : ℝ) : xiLehmanTailMajorant 0 H =
    2 * (1 + 1 / H ^ 2) *
      ((2 + Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 - xiLowReciprocalMass H) := by
  simp only [xiLehmanTailMajorant, ↓reduceIte]

example : xiHeightTail (-30600000000) 100000 ≤ xiLehmanTailMajorant (-30600000000) 100000 := by
  apply xiHeightTail_le_lehmanMajorant (by norm_num)
  intro _
  norm_num

example {ι : Type*} (S : Finset ι) (a k : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i)
    {t H : ℝ} (hH : 0 < H)
    (hA : ∀ i ∈ S, k i * t ≠ 0 → 10 ^ 9 ≤ |k i * t| + H) :
    (∑ i ∈ S, a i * xiHeightTail (k i * t) H) ≤
      ∑ i ∈ S, a i * xiLehmanTailMajorant (k i * t) H :=
  sum_xiHeightTail_le_lehmanMajorant S a k ha hH hA

example (n : ℕ) (a : ℕ → ℝ) (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) :
    (∑ i ∈ Finset.range (n + 1), a i * xiHeightTail ((i : ℝ) * 30600000000) 100000) ≤
      ∑ i ∈ Finset.range (n + 1), a i * xiLehmanTailMajorant ((i : ℝ) * 30600000000) 100000 :=
  sum_xiHeightTail_nat_harmonics_le _ a ha (by norm_num) (by norm_num)

example {t H : ℝ} (ht : 10 ^ 9 ≤ t) (hH : 0 < H) :
    xiHeightTail 0 H + xiHeightTail t H ≤
      xiLehmanTailMajorant 0 H + xiLehmanHighBound t H := by
  exact add_le_add
    (xiHeightTail_le_lehmanMajorant hH (fun hn => (hn rfl).elim))
    (xiHeightTail_le_highBound (by linarith) hH (by linarith))

example {θ η κ σ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hκ : 0 ≤ κ)
    (hσ : 1 / 2 ≤ σ) :
    smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ (1 / 2)
      (((σ : ℂ) + (0 : ℂ) * I) - 1) ≤
      (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
        (kadiriWeightSupport θ η) ((σ - 1 : ℝ) : ℂ)).re :=
  kadiriWeight_pole_zero_le hθ hη hκ (by linarith)

example {θ η κ δ σ z t : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)
    (hκ : 0 ≤ κ) (hσ : σ ≤ 1) (hδ : 0 ≤ σ - 1 + δ)
    (hz : z ≤ (σ - 1) / η) (ht : 0 < t) :
    smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
      (((σ : ℂ) + ((-t : ℝ) : ℂ) * I) - 1) ≤ kadiriPoleError θ η z / t ^ 2 := by
  simpa only [neg_sq] using kadiriWeight_pole_nonzero_le hθ hη hκ hσ hδ hz
    (neg_ne_zero.mpr ht.ne')

example {θ η κ δ σ z : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)
    (hκ : 0 ≤ κ) (hσ : σ ≤ 1) (hδ : 0 ≤ σ - 1 + δ)
    (hz : z ≤ (σ - 1) / η) (n : ℕ) (c : ℕ → ℝ)
    (hc : ∀ i ∈ Finset.range (n + 1), 0 ≤ c i) (t : ℝ) :
    (∑ i ∈ Finset.range (n + 1), c i * smoothedLaplaceDifference (kadiriWeight θ η)
      (kadiriWeightSupport θ η) κ δ (((σ : ℂ) + ((i : ℝ) * t : ℝ) * I) - 1)) ≤
      ∑ i ∈ Finset.range (n + 1), c i * kadiriPoleMajorant θ η z σ ((i : ℝ) * t) :=
  sum_kadiriWeight_pole_le_majorant hθ hη hκ hσ hδ hz _ c (fun i => (i : ℝ)) hc t

end

end PrimeFactorUnimodality.Tests
