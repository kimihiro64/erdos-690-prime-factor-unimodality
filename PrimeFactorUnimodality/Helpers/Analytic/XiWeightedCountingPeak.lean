import PrimeFactorUnimodality.Helpers.Analytic.XiWeightedCountingBounds

/-! # Joining weighted zero-counting bounds at a maximum

The half-open windows partition with multiplicity, even when a zero lies
at the joining height. Adding the signed branch estimates cancels the
actual counting discrepancy there, leaving just twice the envelope times
the peak. Bounding the branches separately would unnecessarily double it.
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Real Set

local instance : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _

/-- A window with coincident endpoints has no divisor labels. -/
@[simp] theorem xiHeightWindowIndices_self (a : ℝ) : xiHeightWindowIndices a a = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro p hp
  have hp' := (mem_xiHeightWindowIndices a a p).mp hp
  exact (not_lt_of_ge hp'.1.2) hp'.2

/-- Adjacent half-open zero windows are disjoint, including their boundary labels. -/
theorem disjoint_xiHeightWindowIndices (a c b : ℝ) :
    Disjoint (xiHeightWindowIndices a c) (xiHeightWindowIndices c b) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hp' := (mem_xiHeightWindowIndices a c p).mp hp
  have hq' := (mem_xiHeightWindowIndices c b p).mp hq
  exact (not_lt_of_ge hp'.1.2) hq'.2

/-- Every label belongs to exactly one of the adjacent windows. -/
theorem xiHeightWindowIndices_union {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    xiHeightWindowIndices a c ∪ xiHeightWindowIndices c b = xiHeightWindowIndices a b := by
  ext p
  simp only [Finset.mem_union, mem_xiHeightWindowIndices]
  constructor
  · rintro (hp | hp)
    · exact ⟨⟨hp.1.1, hp.1.2.trans hcb⟩, hp.2⟩
    · exact ⟨hp.1, hac.trans_lt hp.2⟩
  · intro hp
    by_cases hpc : (riemannXiDivisorZeroValue p).im ≤ c
    · exact Or.inl ⟨⟨hp.1.1, hpc⟩, hp.2⟩
    · exact Or.inr ⟨hp.1, lt_of_not_ge hpc⟩

/-- Summing adjacent windows does not lose or duplicate zeros at the split. -/
theorem sum_xiHeightWindowIndices_add {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (f : RiemannXiDivisorZeroIndex → ℝ) :
    (∑ p ∈ xiHeightWindowIndices a c, f p) +
        (∑ p ∈ xiHeightWindowIndices c b, f p) =
      ∑ p ∈ xiHeightWindowIndices a b, f p := by
  rw [← Finset.sum_union (disjoint_xiHeightWindowIndices a c b),
    xiHeightWindowIndices_union hac hcb]

/-- The signed counting estimate for a function increasing then decreasing. -/
theorem sum_xi_weighted_window_le_of_peak {a c b : ℝ} {f g : ℝ → ℝ}
    (ha : 10 ≤ a) (hac : a ≤ c) (hcb : c ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (g t) t) (hg : ContinuousOn g (Icc a b))
    (hinc : ∀ t ∈ Icc a c, 0 ≤ g t) (hdec : ∀ t ∈ Icc c b, g t ≤ 0) :
    (∑ p ∈ xiHeightWindowIndices a b, f (riemannXiDivisorZeroValue p).im) ≤
      (∫ t in Icc a b, ((1 / (2 * π)) * Real.log (t / (2 * π))) * f t) -
      (∫ t in Icc a c, f t / t) + (∫ t in Icc c b, f t / t) +
      2 * (Real.log c + 17) * f c +
      (xiZeroCountingRemainder b - (Real.log b + 17)) * f b -
      (xiZeroCountingRemainder a + (Real.log a + 17)) * f a := by
  have hleft : Icc a c ⊆ Icc a b := fun _ ht => ⟨ht.1, ht.2.trans hcb⟩
  have hright : Icc c b ⊆ Icc a b := fun _ ht => ⟨hac.trans ht.1, ht.2⟩
  have hi := sum_xi_weighted_window_le_of_slope_nonneg ha hac
    (fun t ht => hf t (hleft ht)) (hg.mono hleft) hinc
  have hd := sum_xi_weighted_window_le_of_slope_nonpos (ha.trans hac) hcb
    (fun t ht => hf t (hright ht)) (hg.mono hright) hdec
  have hcont : ContinuousOn
      (fun t => ((1 / (2 * π)) * Real.log (t / (2 * π))) * f t) (Icc a b) := by
    apply ContinuousOn.mul _ (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    apply continuousOn_const.mul
    apply (continuousOn_id.div_const (2 * π)).log
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact div_ne_zero ht0.ne' (by positivity)
  have hint :
      (∫ t in Icc a c, ((1 / (2 * π)) * Real.log (t / (2 * π))) * f t) +
      (∫ t in Icc c b, ((1 / (2 * π)) * Real.log (t / (2 * π))) * f t) =
      ∫ t in Icc a b, ((1 / (2 * π)) * Real.log (t / (2 * π))) * f t := by
    simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hac,
      ← intervalIntegral.integral_of_le hcb, ← intervalIntegral.integral_of_le (hac.trans hcb)]
    exact intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hac).mpr
        (hcont.mono hleft).integrableOn_Icc)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hcb).mpr
        (hcont.mono hright).integrableOn_Icc)
  have hsum := sum_xiHeightWindowIndices_add hac hcb
    (fun p => f (riemannXiDivisorZeroValue p).im)
  nlinarith only [hi, hd, hint, hsum]

/-- Nonnegative weights allow the outer endpoint terms to be dropped. -/
theorem sum_xi_weighted_window_le_peak_envelope {a c b : ℝ} {f g : ℝ → ℝ}
    (ha : 10 ≤ a) (hac : a ≤ c) (hcb : c ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (g t) t) (hg : ContinuousOn g (Icc a b))
    (hinc : ∀ t ∈ Icc a c, 0 ≤ g t) (hdec : ∀ t ∈ Icc c b, g t ≤ 0)
    (hfa : 0 ≤ f a) (hfb : 0 ≤ f b) :
    (∑ p ∈ xiHeightWindowIndices a b, f (riemannXiDivisorZeroValue p).im) ≤
      (∫ t in Icc a b, ((1 / (2 * π)) * Real.log (t / (2 * π))) * f t) -
      (∫ t in Icc a c, f t / t) + (∫ t in Icc c b, f t / t) +
      2 * (Real.log c + 17) * f c := by
  have he := sum_xi_weighted_window_le_of_peak ha hac hcb hf hg hinc hdec
  have hA := (abs_le.mp (abs_xiZeroCountingRemainder_le_log_add ha)).1
  have hB := (abs_le.mp
    (abs_xiZeroCountingRemainder_le_log_add (ha.trans (hac.trans hcb)))).2
  nlinarith [mul_nonneg (show 0 ≤ xiZeroCountingRemainder a + (Real.log a + 17) by linarith) hfa,
    mul_nonpos_of_nonpos_of_nonneg
      (show xiZeroCountingRemainder b - (Real.log b + 17) ≤ 0 by linarith) hfb]

end

end PrimeFactorUnimodality
