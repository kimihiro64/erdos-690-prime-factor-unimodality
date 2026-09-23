import PrimeFactorUnimodality.Helpers.Analytic.XiReciprocalNormHigh
import PrimeFactorUnimodality.Helpers.Analytic.XiReciprocalNormSymmetry

/-! # An explicit low reciprocal-norm mass from the actual counting theorem

Same-height reflection turns an upper real-part gap into a lower one.
The unconditional exact real reciprocal mass sharpens the small prefix,
while the reciprocal-ordinate Abel estimate controls the rest. Conjugation
handles both signs with all multiplicities.
Only the stated low-height gap remains an input; the norm-mass estimate
is proved here rather than supplied separately.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- Reflection gives the other side of any real-part gap on the strict low set. -/
theorem xi_low_re_ge_of_gap {T δ : ℝ}
    (hgap : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    {p : RiemannXiDivisorZeroIndex} (hp : p ∈ xiLowHeightIndices T) :
    δ ≤ (riemannXiDivisorZeroValue p).re := by
  have hr : riemannXiDivisorSameHeightReflection p ∈ xiLowHeightIndices T := by
    simpa only [mem_xiLowHeightIndices, riemannXiDivisorZeroValue_sameHeightReflection,
      sub_im, one_im, conj_im, sub_neg_eq_add, zero_add] using hp
  have hg := hgap _ hr
  simp only [riemannXiDivisorZeroValue_sameHeightReflection, sub_re, one_re, conj_re] at hg
  linarith

/-- A positive low gap bounds each reciprocal norm in the small prefix. -/
theorem norm_xi_low_reciprocal_le {T δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    {p : RiemannXiDivisorZeroIndex} (hp : p ∈ xiLowHeightIndices T) :
    ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖ ≤ 1 / δ := by
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le hδ ((xi_low_re_ge_of_gap hgap hp).trans (re_le_norm _))

/-- The closed positive prefix lies strictly below the gap cutoff. -/
theorem sum_xi_positive_prefix_reciprocal_norm_le {a T δ : ℝ}
    (haT : a < T) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    (∑ p ∈ xiPositiveHeightIndices a, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      (xiZeroCount a : ℝ) / δ := by
  calc
    _ ≤ ∑ _p ∈ xiPositiveHeightIndices a, (1 / δ : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      apply norm_xi_low_reciprocal_le hδ hgap
      have he := (mem_xiPositiveHeightIndices a p).mp hp
      rw [mem_xiLowHeightIndices, abs_of_pos he.1]
      exact he.2.trans_lt haT
    _ = (xiZeroCount a : ℝ) / δ := by simp [xiZeroCount, div_eq_mul_inv]

/-- A reciprocal norm in the positive prefix is controlled by its real reciprocal atom. -/
theorem norm_xi_positive_prefix_reciprocal_le_mass {a T δ : ℝ}
    (ha : 0 ≤ a) (haT : a < T) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    {p : RiemannXiDivisorZeroIndex} (hp : p ∈ xiPositiveHeightIndices a) :
    ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖ ≤
      ((a + 1) / δ) * (1 / riemannXiDivisorZeroValue p).re := by
  let z := riemannXiDivisorZeroValue p
  have hv := (mem_xiPositiveHeightIndices a p).mp hp
  have hpT : p ∈ xiLowHeightIndices T := by
    rw [mem_xiLowHeightIndices, abs_of_pos hv.1]
    exact hv.2.trans_lt haT
  have hβ : δ ≤ z.re := xi_low_re_ge_of_gap hgap hpT
  obtain ⟨hβ0, hβ1⟩ := riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)
  have hz : 0 < ‖z‖ := norm_pos_iff.mpr (riemannXiDivisorZeroValue_ne_zero p)
  have hn : ‖z‖ ≤ a + 1 := by
    have hn := norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg hβ0, abs_of_pos hv.1] at hn
    linarith
  have hb : δ * ‖z‖ ≤ (a + 1) * z.re :=
    (mul_le_mul_of_nonneg_left hn hδ.le).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hβ (by linarith : 0 ≤ a + 1)])
  change ‖(1 : ℂ) / z‖ ≤ ((a + 1) / δ) * (1 / z).re
  simp only [one_div, norm_inv, inv_re, normSq_eq_norm_sq]
  apply (mul_le_mul_iff_left₀ (mul_pos hδ (sq_pos_of_pos hz))).mp
  convert hb using 1 <;> field_simp

/-- Reuse the unconditional exact real mass instead of a coarse small-height count. -/
theorem sum_xi_positive_prefix_reciprocal_norm_le_mass {a T δ : ℝ}
    (ha : 0 ≤ a) (haT : a < T) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    (∑ p ∈ xiPositiveHeightIndices a, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      ((a + 1) / δ) * ((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2) := by
  have hmass := (sum_reciprocal_le_xiLowReciprocalMass T (xiPositiveHeightIndices a) (by
    intro p hp
    have hv := (mem_xiPositiveHeightIndices a p).mp hp
    rw [abs_of_pos hv.1]
    exact hv.2.trans_lt haT)).trans (xiLowReciprocalMass_le_total T)
  calc
    _ ≤ ∑ p ∈ xiPositiveHeightIndices a, ((a + 1) / δ) *
        (1 / riemannXiDivisorZeroValue p).re :=
      Finset.sum_le_sum (fun p hp => norm_xi_positive_prefix_reciprocal_le_mass ha haT hδ hgap hp)
    _ = ((a + 1) / δ) * ∑ p ∈ xiPositiveHeightIndices a,
        (1 / riemannXiDivisorZeroValue p).re := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (div_nonneg (by linarith) hδ.le)

/-- A fully elementary expression bounding the strict low reciprocal-norm mass. -/
def xiLowReciprocalNormBound (a T δ : ℝ) : ℝ :=
  2 * (min (xiReciprocalCountEnvelope a / δ)
    (((a + 1) / δ) * ((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2)) +
      xiReciprocalNormWindowBound a T)

/-- Counting and the gap suffice: no independent reciprocal-mass hypothesis remains. -/
theorem sum_xi_low_reciprocal_norm_le_explicit {a T δ : ℝ}
    (ha : 10 ≤ a) (haT : a < T) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    (∑ p ∈ xiLowHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      xiLowReciprocalNormBound a T δ := by
  classical
  let : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _
  have hp := (sum_xi_positive_prefix_reciprocal_norm_le haT hδ hgap).trans
    (div_le_div_of_nonneg_right (xiZeroCount_le_reciprocal_envelope ha) hδ.le)
  have hm := sum_xi_positive_prefix_reciprocal_norm_le_mass (by linarith) haT hδ hgap
  have hprefix := le_min hp hm
  have hw := sum_xi_reciprocal_norm_window_le_explicit ha haT.le
  have hs := Finset.sum_sdiff (f := fun p => ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖)
    (xiPositiveHeightIndices_mono haT.le)
  have hwin : xiHeightWindowIndices a T =
      xiPositiveHeightIndices T \ xiPositiveHeightIndices a := xiHeightWindowIndices_eq_sdiff a T
  rw [← hwin] at hs
  have hpos : (∑ p ∈ xiPositiveHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      min (xiReciprocalCountEnvelope a / δ)
        (((a + 1) / δ) * ((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2)) +
          xiReciprocalNormWindowBound a T := by linarith only [hs, hprefix, hw]
  exact (sum_xi_low_reciprocal_norm_le_twice_positive T).trans
    (mul_le_mul_of_nonneg_left hpos (by norm_num))

/-- The exact-mass refinement never exceeds the previous counting-only formula. -/
theorem xiLowReciprocalNormBound_le_counting (a T δ : ℝ) :
    xiLowReciprocalNormBound a T δ ≤
      2 * (xiReciprocalCountEnvelope a / δ + xiReciprocalNormWindowBound a T) :=
  mul_le_mul_of_nonneg_left (add_le_add (min_le_left _ _) le_rfl) (by norm_num)

end

end PrimeFactorUnimodality
