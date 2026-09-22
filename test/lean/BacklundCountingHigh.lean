import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanHigh

/-! # Averaged circle bounds and unconditional high zero-counting regressions

Check signed heights, the leftmost circle point, both count conventions,
and the closed Lehman tail at all positive paper harmonics. No numerical
counting estimate or zero-free cutoff premise is supplied by these tests.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter Real Set
open scoped Topology

example {f : ℂ → ℝ} {c : ℂ} {R B : ℝ} (hf : CircleIntegrable f c R)
    (hb : ∀ z ∈ Metric.sphere c |R|, f z + f (2 * c - z) ≤ B) :
    circleAverage f c R ≤ B / 2 := circleAverage_le_of_antipodal_bound hf hb

example {c : ℂ} {r R : ℝ} (hr : 0 < r) (hR : r < R) (hc : c ≠ 0) :
    ((∑ᶠ u, MeromorphicOn.divisor (fun z : ℂ => z ^ 2) (Metric.closedBall c r) u : ℤ) : ℝ) ≤
      (circleAverage (fun z : ℂ => Real.log ‖z ^ 2‖) c R - Real.log ‖c ^ 2‖) /
        Real.log (R / r) :=
  AnalyticOnNhd.sum_divisor_le_circleAverage hr hR (by fun_prop) (pow_ne_zero 2 hc)

example {T : ℝ} (hT : 10 ≤ |T|) :
    ‖Backlund.zetaSurrogate ((1 / 10 : ℂ) + T * I)‖ ≤ 50 * |T| ^ 2 := by
  apply norm_backlundSurrogate_unit_circle_le hT
  norm_num [Metric.mem_sphere, dist_eq_norm]

example : ‖Backlund.zetaSurrogate ((21 / 10 : ℂ) + (-10 : ℂ) * I)‖ ≤ 220 := by
  have h := norm_backlundSurrogate_unit_right_semicircle_le
    (t := -10) (z := (21 / 10 : ℂ)) (by norm_num)
    (by norm_num [Metric.mem_sphere, dist_eq_norm]) (by norm_num)
  norm_num at h ⊢
  exact h

example {T : ℝ} (hT : 10 ≤ |T|) (n : ℕ) :
    circleAverage (fun z => Real.log ‖backlundAuxiliary T n z‖) (11 / 10 : ℂ) 1 ≤
      (n : ℝ) * backlundCircleLogBound T := circleAverage_log_backlundAuxiliary_le hT n

example {s : ℂ} (hs : 1 < s.re) : ‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ :=
  norm_riemannZeta_le_norm_real hs

example (T : ℝ) : Tendsto (fun x => (xiZeroCount x : ℝ)) (𝓝[<] T)
    (𝓝 (xiStrictZeroCount T : ℝ)) := tendsto_xiZeroCount_left T

example (T : ℝ) : Tendsto (fun x => (xiStrictZeroCount x : ℝ)) (𝓝[>] T)
    (𝓝 (xiZeroCount T : ℝ)) := tendsto_xiStrictZeroCount_right T

example {T : ℝ} (hT : 10 ≤ T) : |xiZeroCountingRemainder T| ≤ Real.log T + 17 :=
  abs_xiZeroCountingRemainder_le_log_add hT

example {T : ℝ} (hT : 10 ^ 9 ≤ T) : |xiZeroCountingRemainder T| ≤ 2 * Real.log T :=
  abs_xiZeroCountingRemainder_le_two_log_high hT

example {T : ℝ} (hT : 10 ^ 9 ≤ T) :
    |(xiStrictZeroCount T : ℝ) - xiZeroCountingMainTerm T| ≤ 2 * Real.log T :=
  abs_xiStrictZeroCount_sub_mainTerm_le_two_log_high hT

example {t H : ℝ} (ht : 0 < t) (hH : 0 < H) (hA : 10 ^ 9 ≤ t + H) :
    xiHeightTail t H ≤ xiLehmanMainIntegral t H + xiLehmanIntegralCorrection t H :=
  xiHeightTail_le_main_add_correction_high ht hH hA

example (k : ℕ) (hk : 1 ≤ k) :
    xiHeightTail ((k : ℝ) * 30600000000) 100000 ≤
      xiLehmanMainIntegral ((k : ℝ) * 30600000000) 100000 +
        xiLehmanIntegralCorrection ((k : ℝ) * 30600000000) 100000 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  apply xiHeightTail_le_main_add_correction_high <;> linarith

end

end PrimeFactorUnimodality.Tests
