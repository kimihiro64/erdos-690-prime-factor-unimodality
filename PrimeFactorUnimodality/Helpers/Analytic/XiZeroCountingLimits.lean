import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingAbel
import PrimeFactorUnimodality.Mathlib.Topology.Algebra.InfiniteSum.Sublevel

/-! # Actual xi tail exhaustion and vanishing counting boundaries

The locally finite divisor gives finite sublevels of each strict positive
tail. Existing summability then gives both convergence of the finite sums
and, for decreasing weights, vanishing of `N(T)f(T)` at infinity. No sharp
zero-counting estimate or RH assumption is used for these limits.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Filter Set
open scoped Topology

/-- A strict positive xi tail has finite sublevels, with every multiplicity label retained. -/
theorem finite_xi_strict_tail_sublevel {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    {p : {p : RiemannXiDivisorZeroIndex // a < (riemannXiDivisorZeroValue p).im} |
      (riemannXiDivisorZeroValue p.1).im ≤ T}.Finite := by
  apply ((finite_xi_divisor_pos_im_le T).preimage_embedding
    (Function.Embedding.subtype _)).subset
  intro p hp
  exact ⟨ha.trans_lt p.2, hp⟩

private theorem xi_strict_tail_sublevel_eq {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    (finite_xi_strict_tail_sublevel ha T).toFinset =
      (xiHeightWindowIndices a T).subtype (fun p => a < (riemannXiDivisorZeroValue p).im) := by
  classical
  ext p
  simp [mem_xiHeightWindowIndices, ha.trans_lt p.2, p.2]

/-- Finite actual ordinate windows exhaust every summable strict positive tail. -/
theorem tendsto_sum_xi_height_window {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ}
    (hs : Summable (fun p : {p : RiemannXiDivisorZeroIndex //
      a < (riemannXiDivisorZeroValue p).im} => f (riemannXiDivisorZeroValue p.1).im)) :
    Tendsto (fun T => ∑ p ∈ xiHeightWindowIndices a T, f (riemannXiDivisorZeroValue p).im)
      atTop (𝓝 (∑' p : {p : RiemannXiDivisorZeroIndex // a < (riemannXiDivisorZeroValue p).im},
        f (riemannXiDivisorZeroValue p.1).im)) := by
  have h := hs.tendsto_sum_sublevel (finite_xi_strict_tail_sublevel ha)
  apply h.congr
  intro T
  rw [xi_strict_tail_sublevel_eq ha T]
  exact Finset.sum_subtype_of_mem (fun p => f (riemannXiDivisorZeroValue p).im)
    (fun p hp => ((mem_xiHeightWindowIndices a T p).mp hp).2)

/-- A nonnegative decreasing summable weight kills the full counting boundary. -/
theorem tendsto_xiZeroCount_mul_of_antitone {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ}
    (hs : Summable (fun p : {p : RiemannXiDivisorZeroIndex //
      a < (riemannXiDivisorZeroValue p).im} => f (riemannXiDivisorZeroValue p.1).im))
    (hpos : ∀ x ∈ Ioi a, 0 ≤ f x) (hmono : AntitoneOn f (Ioi a))
    (hzero : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun T => (xiZeroCount T : ℝ) * f T) atTop (𝓝 0) := by
  classical
  have h := hs.tendsto_card_sublevel_mul_of_antitone (a := a) (fun p => p.2)
    (finite_xi_strict_tail_sublevel ha) hpos hmono hzero
  have hsum := h.add (hzero.const_mul (xiZeroCount a : ℝ))
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from
    by simpa only [mul_zero, add_zero] using hsum).congr'
  filter_upwards [eventually_ge_atTop a] with T hT
  rw [xi_strict_tail_sublevel_eq ha T, Finset.card_subtype,
    Finset.filter_true_of_mem (fun p hp => ((mem_xiHeightWindowIndices a T p).mp hp).2),
    card_xiHeightWindowIndices hT]
  ring

end

end PrimeFactorUnimodality
