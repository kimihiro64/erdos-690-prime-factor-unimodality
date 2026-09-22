import PrimeFactorUnimodality.Helpers.Analytic.XiZetaCountingBounds

/-! # Counting conventions and multiplicity regressions

The strict count matches the sibling API exactly. Closed counts retain the
entire boundary fiber, including at repeated ordinates. The right-limit
theorem and envelope transfer do not assume that the cutoff avoids zeros.
The numerical RvM hypothesis remains visible in every dependent estimate.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter Real Set
open scoped Topology

example (T : ℝ) : (xiStrictZeroCount T : ℝ) = riemannZeta.N T :=
  xiStrictZeroCount_eq_zeta_N T

example {T : ℝ} (hT : 0 < T) :
    (xiZeroCount T : ℝ) - riemannZeta.N T = (xiOrdinateMultiplicity T : ℝ) := by
  rw [xiZeroCount_eq_zeta_N_add_multiplicity hT]
  ring

example (T : ℝ) : Tendsto riemannZeta.N (𝓝[>] T) (𝓝 (xiZeroCount T : ℝ)) :=
  tendsto_zeta_N_right T

example : xiStrictZeroCount 0 = 0 := by
  unfold xiStrictZeroCount
  have h : xiStrictPositiveHeightIndices 0 = ∅ := by
    ext p
    simp only [mem_xiStrictPositiveHeightIndices, Finset.notMem_empty, iff_false]
    exact fun hp => hp.1.not_gt hp.2
  rw [h, Finset.card_empty]

example {s : ℂ} (hi : s.im ≠ 0) (hs : riemannZeta s = 0) :
    0 < s.re ∧ s.re < 1 :=
  riemannXi_zero_mem_open_critical_strip
    (riemannXi_eq_zero_of_zeta_zero_of_im_ne_zero hi hs)

example {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    MeromorphicOn.divisor riemannXi univ s = riemannZeta.order s :=
  xi_divisor_eq_zeta_order hs hs1

example {T : ℝ} (hlog : 5 ≤ Real.log T) :
    riemannZeta.RvM 0.137 0.443 6.1 T + 7 / 8 ≤ 2 * Real.log T :=
  backlund_envelope_add_offset_le_two_log hlog

example (h : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    {A : ℝ} (hA : 2 ≤ A) (hlog : 5 ≤ Real.log A) :
    ∀ x ∈ Ici A, |xiZeroCountingRemainder x| ≤ 2 * Real.log x :=
  xiZeroCountingRemainder_le_two_log_of_rvm h hA hlog

example (h : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    {t H : ℝ} (ht : 0 < t) (hH : 0 < H) (hA : 2 ≤ t + H)
    (hlog : 5 ≤ Real.log (t + H)) (hb : xiOrdinateMultiplicity (t + H) = 0) :
    xiHeightTail t H ≤ xiLehmanMainIntegral t H + xiLehmanIntegralCorrection t H := by
  simpa only [hb, Nat.cast_zero, zero_mul, add_zero] using xiHeightTail_le_of_rvm h ht hH hA hlog

end

end PrimeFactorUnimodality.Tests
