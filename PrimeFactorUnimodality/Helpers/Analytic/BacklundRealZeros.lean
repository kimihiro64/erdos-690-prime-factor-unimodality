import PrimeFactorUnimodality.Helpers.Analytic.BacklundJensen
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.JensenCard

/-! # Bounding the real-part zeros in Backlund's horizontal segment

Count distinct real zeros of the actual auxiliary function on a symmetric
interval. A nonzero centre proves finiteness; each such zero contributes
at least one to the analytic divisor in the containing disk. Thus Jensen's
bound applies to the real-part crossings, not merely an unrelated complex
zero count. Argument variation and the explicit boundary norm estimate
remain subsequent analytic steps.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter Metric Real Set
open scoped Topology

/-- The real-part crossings in the closed horizontal interval centred at `σ`. -/
def backlundRealZeros (T : ℝ) (n : ℕ) (σ r : ℝ) : Set ℝ :=
  {x | |x - σ| ≤ r ∧ (Backlund.zetaSurrogate ((x : ℂ) + T * I) ^ n).re = 0}

/-- The number of distinct crossings, with finiteness proved before using the count. -/
def backlundRealZeroCount (T : ℝ) (n : ℕ) (σ r : ℝ) : ℕ :=
  (backlundRealZeros T n σ r).ncard

/-- A nonzero centre excludes the identically-zero case and makes the crossing set finite. -/
theorem finite_backlundRealZeros {T σ r : ℝ} {n : ℕ} (hr : 0 ≤ r)
    (hc : backlundAuxiliary T n σ ≠ 0) : (backlundRealZeros T n σ r).Finite := by
  have ha : AnalyticOnNhd ℂ (backlundAuxiliary T n) (closedBall (σ : ℂ) r) :=
    fun z _ => (differentiable_backlundAuxiliary T n).analyticAt z
  have hf := ha.finite_zeros_of_isCompact_of_isPreconnected (isCompact_closedBall _ _)
    (convex_closedBall (σ : ℂ) r).isPreconnected (mem_closedBall_self hr) hc
  have hpre := hf.preimage Complex.ofReal_injective.injOn
  have heq : backlundRealZeros T n σ r =
      Complex.ofReal ⁻¹' {z ∈ closedBall (σ : ℂ) r | backlundAuxiliary T n z = 0} := by
    ext x
    simp only [backlundRealZeros, mem_ofPred_eq, mem_preimage, mem_closedBall,
      Complex.isometry_ofReal.dist_eq, Real.dist_eq, backlundAuxiliary_ofReal_eq_zero_iff]
  rw [heq]
  exact hpre

/-- Each distinct crossing contributes a positive integer to the containing disk's divisor. -/
theorem backlundRealZeroCount_le_mass {T σ r : ℝ} {n : ℕ} (hr : 0 ≤ r)
    (hc : backlundAuxiliary T n σ ≠ 0) :
    (backlundRealZeroCount T n σ r : ℝ) ≤ backlundAuxiliaryZeroMass T n σ r := by
  classical
  let S := (finite_backlundRealZeros hr hc).toFinset
  have ha : AnalyticOnNhd ℂ (backlundAuxiliary T n) (closedBall (σ : ℂ) r) :=
    fun z _ => (differentiable_backlundAuxiliary T n).analyticAt z
  have h := ha.card_zeros_le_sum_divisor (isCompact_closedBall _ _)
    (convex_closedBall (σ : ℂ) r).isPreconnected (mem_closedBall_self hr) hc
    (S.image Complex.ofReal) (by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      have hx' : x ∈ backlundRealZeros T n σ r :=
        (finite_backlundRealZeros hr hc).mem_toFinset.mp hx
      refine ⟨?_, (backlundAuxiliary_ofReal_eq_zero_iff T x n).mpr hx'.2⟩
      simpa only [mem_closedBall, Complex.isometry_ofReal.dist_eq, Real.dist_eq] using hx'.1)
  rw [Finset.card_image_of_injective S Complex.ofReal_injective] at h
  have hcard : S.card = backlundRealZeroCount T n σ r :=
    (Set.ncard_eq_toFinset_card _ (finite_backlundRealZeros hr hc)).symm
  rw [hcard] at h
  unfold backlundAuxiliaryZeroMass
  exact_mod_cast h

/-- The real-part zero count satisfies the same explicit Jensen bound at every good power. -/
theorem backlundRealZeroCount_le {σ T r R M : ℝ} {n : ℕ}
    (hσ : 1 < σ) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hc : ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖ ^ n / 2 ≤
      ‖backlundAuxiliary T n σ‖)
    (hp : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    (backlundRealZeroCount T n σ r : ℝ) ≤
      ((n : ℝ) * Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) + Real.log 2) /
        Real.log (R / r) := by
  have hA : 0 < ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖ :=
    norm_pos_iff.mpr (backlund_surrogate_ne_zero_of_one_lt_re (by simpa using hσ))
  have hn : backlundAuxiliary T n σ ≠ 0 :=
    norm_pos_iff.mp ((div_pos (pow_pos hA n) (by norm_num)).trans_le hc)
  exact (backlundRealZeroCount_le_mass hr.le hn).trans
    (backlundAuxiliaryZeroMass_le hσ hr hrR hM hc hp hm)

/-- The real-part crossing estimate is available at arbitrarily large powers. -/
theorem frequently_backlundRealZeroCount_le {σ T r R M : ℝ}
    (hσ : 1 < σ) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hp : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    ∃ᶠ n : ℕ in atTop, (backlundRealZeroCount T n σ r : ℝ) ≤
      ((n : ℝ) * Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) + Real.log 2) /
        Real.log (R / r) :=
  (frequently_backlundAuxiliary_centre_lower hσ T).mono fun _ hc =>
    backlundRealZeroCount_le hσ hr hrR hM hc hp hm

end

end PrimeFactorUnimodality
