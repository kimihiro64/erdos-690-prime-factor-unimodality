import PrimeFactorUnimodality.Helpers.Analytic.XiHeightTailEndpoint
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingRemainder

/-! # Strict counts, cutoff multiplicity, and transfer of counting estimates

The integral layer counts positive ordinates through a closed upper cutoff.
Strict counts approach this value from the right, by local finiteness of
the actual divisor. Thus continuous quantitative bounds on strict counts
transfer to closed counts, including at zero heights, without assuming
that the cutoff is free of zeros.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Filter Real Set
open scoped Topology

/-- Positive xi divisor labels strictly below the upper cutoff. -/
def xiStrictPositiveHeightIndices (T : ℝ) : Finset RiemannXiDivisorZeroIndex :=
  (xiPositiveHeightIndices T).filter (fun p => (riemannXiDivisorZeroValue p).im < T)

@[simp] theorem mem_xiStrictPositiveHeightIndices (T : ℝ) (p : RiemannXiDivisorZeroIndex) :
    p ∈ xiStrictPositiveHeightIndices T ↔
      0 < (riemannXiDivisorZeroValue p).im ∧ (riemannXiDivisorZeroValue p).im < T := by
  simp only [xiStrictPositiveHeightIndices, Finset.mem_filter, mem_xiPositiveHeightIndices]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.le⟩, h.2⟩⟩

/-- The strict positive-height count, with every multiplicity label. -/
def xiStrictZeroCount (T : ℝ) : ℕ := (xiStrictPositiveHeightIndices T).card

/-- At a positive cutoff the closed count adds exactly the full ordinate multiplicity. -/
theorem xiZeroCount_eq_strict_add_multiplicity {T : ℝ} (hT : 0 < T) :
    xiZeroCount T = xiStrictZeroCount T + xiOrdinateMultiplicity T := by
  classical
  have hb : (xiPositiveHeightIndices T).filter
      (fun p => ¬(riemannXiDivisorZeroValue p).im < T) =
        (finite_xi_divisor_im_eq T).toFinset := by
    ext p
    simp only [Finset.mem_filter, mem_xiPositiveHeightIndices, not_lt, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq]
    exact ⟨fun h => le_antisymm h.1.2 h.2, fun h => by rw [h]; exact ⟨⟨hT, le_rfl⟩, le_rfl⟩⟩
  have hc := Finset.card_filter_add_card_filter_not (s := xiPositiveHeightIndices T)
    (fun p => (riemannXiDivisorZeroValue p).im < T)
  rw [hb, ← Set.ncard_eq_toFinset_card _ (finite_xi_divisor_im_eq T)] at hc
  change xiZeroCount T = xiStrictZeroCount T +
    ({p : RiemannXiDivisorZeroIndex | (riemannXiDivisorZeroValue p).im = T} : Set _).ncard
  exact hc.symm

/-- Immediately to the right of a cutoff, strict labels are exactly its closed labels. -/
theorem eventually_xiStrictPositiveHeightIndices_eq (T : ℝ) :
    ∀ᶠ x in 𝓝[>] T, xiStrictPositiveHeightIndices x = xiPositiveHeightIndices T := by
  have hgap : ∀ᶠ x in 𝓝 T, ∀ p ∈ xiPositiveHeightIndices (T + 1),
      T < (riemannXiDivisorZeroValue p).im → x < (riemannXiDivisorZeroValue p).im := by
    apply (Finset.eventually_all _).mpr
    intro p _
    by_cases hp : T < (riemannXiDivisorZeroValue p).im
    · exact (eventually_lt_nhds hp).mono (fun _ hx _ => hx)
    · exact Eventually.of_forall (fun _ hx => (hp hx).elim)
  filter_upwards [hgap.filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (show T < T + 1 by linarith)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with x hg hx hTx
  have hTx' : T < x := hTx
  ext p
  rw [mem_xiStrictPositiveHeightIndices, mem_xiPositiveHeightIndices]
  constructor
  · rintro ⟨hp, hpx⟩
    refine ⟨hp, le_of_not_gt ?_⟩
    intro hpT
    have hpS : p ∈ xiPositiveHeightIndices (T + 1) :=
      (mem_xiPositiveHeightIndices _ _).mpr ⟨hp, (hpx.trans hx).le⟩
    exact (hg p hpS hpT).not_gt hpx
  · rintro ⟨hp, hpT⟩
    exact ⟨hp, hpT.trans_lt hTx'⟩

/-- The strict count has the closed count as its right-hand limit. -/
theorem tendsto_xiStrictZeroCount_right (T : ℝ) :
    Tendsto (fun x => (xiStrictZeroCount x : ℝ)) (𝓝[>] T) (𝓝 (xiZeroCount T : ℝ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_xiStrictPositiveHeightIndices_eq T] with x hx
  simp only [xiStrictZeroCount, xiZeroCount, hx]

/-- A continuous error envelope for strict counts also holds at the closed cutoff. -/
theorem xiZeroCount_error_le_of_strict {P B : ℝ → ℝ} {T : ℝ}
    (hP : ContinuousAt P T) (hB : ContinuousAt B T)
    (h : ∀ᶠ x in 𝓝[>] T, |(xiStrictZeroCount x : ℝ) - P x| ≤ B x) :
    |(xiZeroCount T : ℝ) - P T| ≤ B T := by
  exact le_of_tendsto_of_tendsto
    ((tendsto_xiStrictZeroCount_right T).sub
      (hP.tendsto.mono_left nhdsWithin_le_nhds)).abs
    (hB.tendsto.mono_left nhdsWithin_le_nhds) h

/-- Immediately to the left, the closed labels are exactly the strict labels at the cutoff. -/
theorem eventually_xiPositiveHeightIndices_eq_left (T : ℝ) :
    ∀ᶠ x in 𝓝[<] T, xiPositiveHeightIndices x = xiStrictPositiveHeightIndices T := by
  have hgap : ∀ᶠ x in 𝓝 T, ∀ p ∈ xiStrictPositiveHeightIndices T,
      (riemannXiDivisorZeroValue p).im < x := by
    apply (Finset.eventually_all _).mpr
    intro p hp
    exact eventually_gt_nhds ((mem_xiStrictPositiveHeightIndices _ _).mp hp).2
  filter_upwards [hgap.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hg hx
  have hx' : x < T := hx
  ext p
  rw [mem_xiPositiveHeightIndices, mem_xiStrictPositiveHeightIndices]
  constructor
  · rintro ⟨hp, hpx⟩
    exact ⟨hp, hpx.trans_lt hx'⟩
  · rintro ⟨hp, hpT⟩
    exact ⟨hp, (hg p ((mem_xiStrictPositiveHeightIndices _ _).mpr ⟨hp, hpT⟩)).le⟩

/-- The strict multiplicity-counted value is the left limit of the closed count. -/
theorem tendsto_xiZeroCount_left (T : ℝ) :
    Tendsto (fun x => (xiZeroCount x : ℝ)) (𝓝[<] T) (𝓝 (xiStrictZeroCount T : ℝ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_xiPositiveHeightIndices_eq_left T] with x hx
  simp only [xiStrictZeroCount, xiZeroCount, hx]

/-- Continuous bounds on closed counts transfer to the strict count without an extra atom. -/
theorem xiStrictZeroCount_error_le_of_closed {P B : ℝ → ℝ} {T : ℝ}
    (hP : ContinuousAt P T) (hB : ContinuousAt B T)
    (h : ∀ᶠ x in 𝓝[<] T, |(xiZeroCount x : ℝ) - P x| ≤ B x) :
    |(xiStrictZeroCount T : ℝ) - P T| ≤ B T :=
  le_of_tendsto_of_tendsto
    ((tendsto_xiZeroCount_left T).sub (hP.tendsto.mono_left nhdsWithin_le_nhds)).abs
    (hB.tendsto.mono_left nhdsWithin_le_nhds) h

/-- In particular, a proved strict logarithmic estimate supplies the actual Lehman premise. -/
theorem xiZeroCountingRemainder_le_of_strict {A : ℝ} (hA : 0 < A)
    (h : ∀ x, A < x → |(xiStrictZeroCount x : ℝ) - xiZeroCountingMainTerm x| ≤
      2 * Real.log x) :
    ∀ x ∈ Ici A, |xiZeroCountingRemainder x| ≤ 2 * Real.log x := by
  intro T hT
  have hTpos : 0 < T := hA.trans_le hT
  apply xiZeroCount_error_le_of_strict
    (hasDerivAt_xiZeroCountingMainTerm hTpos).continuousAt
    (continuousAt_const.mul (Real.continuousAt_log hTpos.ne'))
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact h x (lt_of_le_of_lt hT hx)

end

end PrimeFactorUnimodality
