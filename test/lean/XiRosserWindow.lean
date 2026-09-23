import PrimeFactorUnimodality.Helpers.Analytic.XiRosserWindow

/-! # Rosser windows: cutoff labels, empty windows, turning points and actual sums -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open MeasureTheory Real Set

local instance : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _

example (a : ℝ) : xiHeightWindowIndices a a = ∅ := by simp

example {a c b : ℝ} (ha : 0 < a) (hac : a < c)
    {p : RiemannXiDivisorZeroIndex} (hp : (riemannXiDivisorZeroValue p).im = c) :
    p ∈ xiHeightWindowIndices a c ∧ p ∉ xiHeightWindowIndices c b := by
  simp only [mem_xiHeightWindowIndices, hp]
  exact ⟨⟨⟨ha.trans hac, le_rfl⟩, hac⟩, fun h => (lt_irrefl c) h.2⟩

example {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    xiHeightWindowIndices a c ∪ xiHeightWindowIndices c b = xiHeightWindowIndices a b :=
  xiHeightWindowIndices_union hac hcb

example (a c b : ℝ) :
    Disjoint (xiHeightWindowIndices a c) (xiHeightWindowIndices c b) :=
  disjoint_xiHeightWindowIndices a c b

example {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (f : RiemannXiDivisorZeroIndex → ℝ) :
    (∑ p ∈ xiHeightWindowIndices a c, f p) + (∑ p ∈ xiHeightWindowIndices c b, f p) =
      ∑ p ∈ xiHeightWindowIndices a b, f p := sum_xiHeightWindowIndices_add hac hcb f

example (a q u : ℝ) : xiRosserWindowBound a q u u = 0 := by simp

example {a q u v : ℝ} (huv : u ≤ v) : xiRosserPeak a q u v ∈ Icc u v :=
  xiRosserPeak_mem huv

example {a q u v : ℝ} (huv : u ≤ v) (hv : v ≤ exp (sqrt (a / q))) :
    xiRosserPeak a q u v = v := by simp [xiRosserPeak, min_eq_left hv, max_eq_right huv]

example {a q u v : ℝ} (hu : exp (sqrt (a / q)) ≤ u) : xiRosserPeak a q u v = u :=
  max_eq_left ((min_le_right _ _).trans hu)

example {a q u v : ℝ} (hu : u ≤ exp (sqrt (a / q))) (hv : exp (sqrt (a / q)) ≤ v) :
    xiRosserPeak a q u v = exp (sqrt (a / q)) := by
  simp [xiRosserPeak, min_eq_right hv, max_eq_right hu]

example {a q u v : ℝ} (ha : 0 ≤ a) (hq : 0 < q) (hu : 10 ≤ u) (huv : u ≤ v) :
    (∑ p ∈ xiHeightWindowIndices u v, logDampedPower a q (riemannXiDivisorZeroValue p).im) ≤
      xiRosserWindowBound a q u v := sum_xi_logDampedPower_le ha hq hu huv

example {q u v : ℝ} (hq : 0 < q) (hu : 10 ≤ u) (huv : u ≤ v) :
    0 ≤ xiRosserWindowBound 0 q u v := xiRosserWindowBound_nonneg le_rfl hq hu huv

example {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (∫ t in Icc u v, 1 / t) = Real.log v - Real.log u := by
  have he := integral_log_count_envelope_mul_deriv (f := fun _ => (1 : ℝ))
    (g := fun _ => 0) hu huv (fun t _ => hasDerivAt_const t 1) continuousOn_const
  simp only [mul_zero, integral_zero, mul_one] at he
  linarith

end

end PrimeFactorUnimodality.Tests
