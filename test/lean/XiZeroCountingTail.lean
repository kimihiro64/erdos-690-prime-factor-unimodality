import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanAbel

/-! # Infinite zero-counting tail regressions

Sublevel exhaustion preserves distinct labels at a repeated real height.
The zero-height specialization checks the decay of the actual counting
boundary. Both strict and closed tail formulas retain their endpoints.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

example (c : Fin 2 → ℝ) :
    Tendsto (fun T : ℝ => ∑ i ∈ (Set.toFinite {_i : Fin 2 | (1 : ℝ) ≤ T}).toFinset, c i)
      atTop (𝓝 (∑ i, c i)) := by
  simpa only [tsum_fintype] using
    (hasSum_fintype c).summable.tendsto_sum_sublevel (r := fun _ => (1 : ℝ))
      (fun T => Set.toFinite {_i : Fin 2 | (1 : ℝ) ≤ T})

example {H : ℝ} (hH : 0 < H) :
    Tendsto (fun T => (xiZeroCount T : ℝ) * (2 / T ^ 2)) atTop (𝓝 0) := by
  have h := tendsto_xiZeroCount_mul_reciprocalSquarePair (t := 0) (by norm_num) hH
  apply h.congr
  intro T
  simp only [Real.reciprocalSquarePair, sub_zero, add_zero]
  ring

example {t H : ℝ} (ht : 0 ≤ t) (hH : 0 < H) :
    IntegrableOn (fun x => (xiZeroCount x : ℝ) * (2 / (x - t) ^ 3 + 2 / (x + t) ^ 3))
      (Ioi (t + H)) :=
  (xi_strict_pair_tail_eq_count_integral ht hH).1

example {t H : ℝ} (ht : 0 ≤ t) (hH : 0 < H) :
    xiHeightTail t H =
      (∫ x in Ioi (t + H), (xiZeroCount x : ℝ) * (2 / (x - t) ^ 3 + 2 / (x + t) ^ 3)) +
        ((xiOrdinateMultiplicity (t + H) : ℝ) - xiZeroCount (t + H)) *
          Real.reciprocalSquarePair t (t + H) := by
  rw [xiHeightTail_eq_count_integral_add_boundary ht hH]
  ring

example {t H : ℝ} (ht : 0 ≤ t) (hH : 0 < H)
    (hb : xiOrdinateMultiplicity (t + H) = 0) :
    xiHeightTail t H =
      (∫ x in Ioi (t + H), (xiZeroCount x : ℝ) * (2 / (x - t) ^ 3 + 2 / (x + t) ^ 3)) -
        (xiZeroCount (t + H) : ℝ) * Real.reciprocalSquarePair t (t + H) := by
  simp only [xiHeightTail_eq_count_integral_add_boundary ht hH, hb,
    Nat.cast_zero, zero_mul, add_zero]

end

end PrimeFactorUnimodality.Tests
