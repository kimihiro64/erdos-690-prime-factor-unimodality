import PrimeFactorUnimodality.Helpers.Analytic.XiReciprocalNormHigh
import PrimeFactorUnimodality.Helpers.Analytic.XiReciprocalNormSymmetry

/-! # A closed-lower, strict-upper band of actual xi zeros

The band complements the strict low set without losing zeros at either
cutoff. Conjugation reduces its reciprocal-norm mass to a positive window.
The lower endpoint of that majorizing window is halved so zeros exactly
at the band boundary remain included, with their analytic multiplicities.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

local instance : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _

/-- All divisor labels with absolute ordinate in `[a,b)`. -/
def xiHeightBandIndices (a b : ℝ) : Finset RiemannXiDivisorZeroIndex :=
  (xiLowHeightIndices b).filter (fun p => a ≤ |(riemannXiDivisorZeroValue p).im|)

@[simp] theorem mem_xiHeightBandIndices (a b : ℝ) (p : RiemannXiDivisorZeroIndex) :
    p ∈ xiHeightBandIndices a b ↔
      a ≤ |(riemannXiDivisorZeroValue p).im| ∧ |(riemannXiDivisorZeroValue p).im| < b := by
  classical
  simp [xiHeightBandIndices, and_comm]

/-- The strict prefix and the band partition the larger strict low set. -/
theorem xiLowHeightIndices_union_band {a b : ℝ} (hab : a ≤ b) :
    xiLowHeightIndices a ∪ xiHeightBandIndices a b = xiLowHeightIndices b := by
  classical
  ext p
  simp only [Finset.mem_union, mem_xiLowHeightIndices, mem_xiHeightBandIndices]
  constructor
  · rintro (h | h)
    · exact h.trans_le hab
    · exact h.2
  · intro h
    by_cases ha : |(riemannXiDivisorZeroValue p).im| < a
    · exact Or.inl ha
    · exact Or.inr ⟨le_of_not_gt ha, h⟩

theorem disjoint_xiLowHeightIndices_band (a b : ℝ) :
    Disjoint (xiLowHeightIndices a) (xiHeightBandIndices a b) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hq
  exact (not_lt_of_ge ((mem_xiHeightBandIndices a b p).mp hq).1)
    ((mem_xiLowHeightIndices a p).mp hp)

/-- Equal cutoffs leave no intermediate zeros, including boundary zeros. -/
@[simp] theorem xiHeightBandIndices_self (a : ℝ) : xiHeightBandIndices a a = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro p hp
  obtain ⟨hlo, hhi⟩ := (mem_xiHeightBandIndices a a p).mp hp
  exact (not_lt_of_ge hlo) hhi

/-- Any nonnegative conjugation-invariant weight fits in two positive windows. -/
theorem sum_xi_band_le_twice_window {a b : ℝ} (ha : 0 < a)
    {f : RiemannXiDivisorZeroIndex → ℝ} (hf : ∀ p, 0 ≤ f p)
    (hc : ∀ p, f (riemannXiDivisorConjugation p) = f p) :
    (∑ p ∈ xiHeightBandIndices a b, f p) ≤
      2 * ∑ p ∈ xiHeightWindowIndices (a / 2) b, f p := by
  classical
  let P := xiHeightWindowIndices (a / 2) b
  let e := riemannXiDivisorConjugation
  have hcover : xiHeightBandIndices a b ⊆ P ∪ P.map e.toEmbedding := by
    intro p hp
    obtain ⟨hlo, hhi⟩ := (mem_xiHeightBandIndices a b p).mp hp
    by_cases hi : 0 < (riemannXiDivisorZeroValue p).im
    · rw [abs_of_pos hi] at hlo hhi
      exact Finset.mem_union_left _ ((mem_xiHeightWindowIndices (a / 2) b p).mpr
        ⟨⟨hi, hhi.le⟩, by linarith⟩)
    · have hi' : (riemannXiDivisorZeroValue p).im < 0 :=
        lt_of_le_of_ne (le_of_not_gt hi) (xi_divisor_im_ne_zero p)
      rw [abs_of_neg hi'] at hlo hhi
      have hv : (riemannXiDivisorZeroValue (e.symm p)).im =
          -(riemannXiDivisorZeroValue p).im := by
        have hc := congrArg Complex.im (riemannXiDivisorZeroValue_conjugation (e.symm p))
        change (riemannXiDivisorZeroValue (e (e.symm p))).im =
          -(riemannXiDivisorZeroValue (e.symm p)).im at hc
        rw [e.apply_symm_apply] at hc
        linarith
      apply Finset.mem_union_right
      apply Finset.mem_map.mpr
      refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
      rw [mem_xiHeightWindowIndices, hv]
      exact ⟨⟨by linarith, hhi.le⟩, by linarith⟩
  have hd : Disjoint P (P.map e.toEmbedding) := by
    rw [Finset.disjoint_left]
    intro p hp hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hn
    have hp' := ((mem_xiHeightWindowIndices (a / 2) b _).mp hp).1.1
    have hq' := ((mem_xiHeightWindowIndices (a / 2) b _).mp hq).1.1
    change 0 < (riemannXiDivisorZeroValue (riemannXiDivisorConjugation q)).im at hp'
    rw [riemannXiDivisorZeroValue_conjugation, conj_im] at hp'
    linarith
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hcover
    (fun p _ _ => hf p)
  rw [Finset.sum_union hd, Finset.sum_map] at hs
  simp only [Equiv.toEmbedding_apply, e, hc] at hs
  simpa only [two_mul] using hs

/-- Both ordinate signs in the band fit in two conjugate positive windows. -/
theorem sum_xi_band_reciprocal_norm_le_twice_window {a b : ℝ} (ha : 0 < a) :
    (∑ p ∈ xiHeightBandIndices a b, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      2 * ∑ p ∈ xiHeightWindowIndices (a / 2) b,
        ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖ :=
  sum_xi_band_le_twice_window ha (fun _ => norm_nonneg _) norm_xi_reciprocal_conjugation

/-- The band mass is controlled by counting, with no real-part gap hypothesis. -/
theorem sum_xi_band_reciprocal_norm_le_explicit {a b : ℝ}
    (ha : 20 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ xiHeightBandIndices a b, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      2 * xiReciprocalNormWindowBound (a / 2) b :=
  (sum_xi_band_reciprocal_norm_le_twice_window (by linarith : 0 < a)).trans
    (mul_le_mul_of_nonneg_left
      (sum_xi_reciprocal_norm_window_le_explicit (by linarith) (by linarith)) (by norm_num))

/-- Keep the exact zero cost when the two cutoffs coincide. -/
def xiBandReciprocalNormBound (a b : ℝ) : ℝ :=
  if a < b then 2 * xiReciprocalNormWindowBound (a / 2) b else 0

@[simp] theorem xiBandReciprocalNormBound_self (a : ℝ) :
    xiBandReciprocalNormBound a a = 0 := by simp [xiBandReciprocalNormBound]

theorem sum_xi_band_reciprocal_norm_le_bound {a b : ℝ}
    (ha : 20 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ xiHeightBandIndices a b, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      xiBandReciprocalNormBound a b := by
  by_cases hlt : a < b
  · simpa only [xiBandReciprocalNormBound, ite_eq_left hlt] using
      sum_xi_band_reciprocal_norm_le_explicit ha hab
  · have he : a = b := le_antisymm hab (le_of_not_gt hlt)
    subst b
    simp

end

end PrimeFactorUnimodality
