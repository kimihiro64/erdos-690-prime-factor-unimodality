import PrimeFactorUnimodality.Helpers.Analytic.XiZetaCountingBridge

/-! # Zero-free horizontal contours immediately above each cutoff

Local finiteness of the actual positive xi divisor leaves an interval
immediately above any nonnegative height with no zero ordinates. Counting
estimates proved using regular contours therefore extend to every cutoff
by the existing strict-to-closed right limit, retaining all multiplicities.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter Set
open scoped Topology

/-- Immediately above a nonnegative cutoff, all horizontal contours avoid xi zeros. -/
theorem eventually_xi_horizontal_nonzero {T : ℝ} (hT : 0 ≤ T) :
    ∀ᶠ x in 𝓝[>] T, ∀ z : ℂ, z.im = x → riemannXi z ≠ 0 := by
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
  change T < x at hTx
  intro z hz hzero
  obtain ⟨p, hp⟩ := exists_xi_divisor_index_of_zero hzero
  have hpim : (riemannXiDivisorZeroValue p).im = x := by rw [hp, hz]
  have hpos : 0 < x := lt_of_le_of_lt hT hTx
  have hpS : p ∈ xiPositiveHeightIndices (T + 1) :=
    (mem_xiPositiveHeightIndices _ _).mpr (by rw [hpim]; exact ⟨hpos, hx.le⟩)
  have hbad := hg p hpS (by simpa only [hpim] using hTx)
  simp only [hpim, lt_self_iff_false] at hbad

/-- A continuous error envelope proved at regular heights also bounds the closed count. -/
theorem xiZeroCount_error_le_of_regular_heights {P B : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hP : ContinuousAt P T) (hB : ContinuousAt B T)
    (h : ∀ x, T < x → (∀ z : ℂ, z.im = x → riemannXi z ≠ 0) →
      |riemannZeta.N x - P x| ≤ B x) :
    |(xiZeroCount T : ℝ) - P T| ≤ B T := by
  apply xiZeroCount_error_le_of_strict hP hB
  filter_upwards [eventually_xi_horizontal_nonzero hT, self_mem_nhdsWithin] with x hx hTx
  simpa only [xiStrictZeroCount_eq_zeta_N] using h x hTx hx

end

end PrimeFactorUnimodality
