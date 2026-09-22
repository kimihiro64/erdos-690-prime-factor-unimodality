import PrimeFactorUnimodality.Helpers.Analytic.XiHeightTailZero
import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanHigh

/-! # A proved tail majorant for all harmonics of the weighted master

At nonzero heights the closed Lehman tail is bounded by an elementary
logarithmic expression. At height zero the exact finite low reciprocal
mass is subtracted from the unconditional Hadamard constant. This assembles
the two cases without assuming a numerical counting theorem, excluding
cutoff zeros, or substituting an RH-dependent inverse-square evaluation.
The finite low mass still needs a numerical lower bound.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The elementary positive-height Lehman expression, after evaluating the integrals. -/
def xiLehmanHighBound (t H : ℝ) : ℝ :=
  (1 / (2 * π)) * (Real.log ((H + t) / (2 * π)) * (1 / H + 1 / (H + 2 * t)) +
    Real.log ((H + 2 * t) / H) / t) +
  4 * Real.log (t + H) * (1 / H ^ 2 + 1 / (H + 2 * t) ^ 2) + 4 / (t * H)

/-- The actual positive-height tail has a bound with no remaining improper integral. -/
theorem xiHeightTail_le_highBound {t H : ℝ}
    (ht : 0 < t) (hH : 0 < H) (hA : 10 ^ 9 ≤ t + H) :
    xiHeightTail t H ≤ xiLehmanHighBound t H :=
  (xiHeightTail_le_main_add_correction_high ht hH hA).trans
    (xiLehmanMainIntegral_add_correction_le ht hH)

/-- The zero harmonic uses exact finite subtraction; other harmonics use the high bound. -/
def xiLehmanTailMajorant (t H : ℝ) : ℝ :=
  if t = 0 then
    2 * (1 + 1 / H ^ 2) *
      ((2 + Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 - xiLowReciprocalMass H)
  else xiLehmanHighBound |t| H

/-- The combined majorant applies to signed heights and retains the zero harmonic. -/
theorem xiHeightTail_le_lehmanMajorant {t H : ℝ} (hH : 0 < H)
    (hA : t ≠ 0 → 10 ^ 9 ≤ |t| + H) :
    xiHeightTail t H ≤ xiLehmanTailMajorant t H := by
  by_cases ht : t = 0
  · subst t
    simpa only [xiLehmanTailMajorant, ↓reduceIte] using
      xiHeightTail_zero_le_reciprocal_mass hH
  · simp only [xiLehmanTailMajorant, ht, ↓reduceIte]
    rw [← xiHeightTail_abs hH t]
    exact xiHeightTail_le_highBound (abs_pos.mpr ht) hH (hA ht)

/-- Nonnegative coefficients preserve the combined zero and positive-height estimates. -/
theorem sum_xiHeightTail_le_lehmanMajorant {ι : Type*} (S : Finset ι)
    (a k : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) {t H : ℝ} (hH : 0 < H)
    (hA : ∀ i ∈ S, k i * t ≠ 0 → 10 ^ 9 ≤ |k i * t| + H) :
    (∑ i ∈ S, a i * xiHeightTail (k i * t) H) ≤
      ∑ i ∈ S, a i * xiLehmanTailMajorant (k i * t) H :=
  Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
    (xiHeightTail_le_lehmanMajorant hH (hA i hi)) (ha i hi))

/-- Every natural harmonic qualifies once the base height is high; zero is included. -/
theorem sum_xiHeightTail_nat_harmonics_le (S : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) {t H : ℝ} (ht : 10 ^ 9 ≤ t) (hH : 0 < H) :
    (∑ i ∈ S, a i * xiHeightTail ((i : ℝ) * t) H) ≤
      ∑ i ∈ S, a i * xiLehmanTailMajorant ((i : ℝ) * t) H := by
  apply sum_xiHeightTail_le_lehmanMajorant S a (fun i => (i : ℝ)) ha hH
  intro i _ hi
  have hi₀ : i ≠ 0 := by
    intro he
    apply hi
    simp [he]
  have hi₁ : (1 : ℝ) ≤ i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi₀
  have hit : 0 ≤ (i : ℝ) * t := mul_nonneg (Nat.cast_nonneg i) (by linarith)
  rw [abs_of_nonneg hit]
  nlinarith

end

end PrimeFactorUnimodality
