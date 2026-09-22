import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingRemainder

/-! # Real-location Abel and actual counting-error regressions

Repeated heights are kept as separate labels; signed weights are allowed.
The half-open window excludes its lower endpoint and retains its upper
endpoint. The constant test function checks both signs in the counting
discrepancy identity.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open MeasureTheory Real Set

-- Two distinct labels at the same real height, with arbitrary signed weights.
example (c : Fin 2 → ℝ) :
    (∫ x in Icc (1 : ℝ) 2, (∑ i ∈ Finset.univ with (1 : ℝ) ≤ x, c i)) = ∑ i, c i := by
  classical
  have h := Finset.sum_mul_eq_sum_mul_sub_integral_count
    (a := 1) (b := 2) (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℝ)) c
    (by intro i _; norm_num) (f := fun x : ℝ => x) (g := fun _ => (1 : ℝ))
    (fun x _ => hasDerivAt_id x) continuousOn_const.integrableOn_Icc
  simp only [mul_one] at h
  linarith

example {a b : ℝ} {p : RiemannXiDivisorZeroIndex}
    (hp : (riemannXiDivisorZeroValue p).im = a) : p ∉ xiHeightWindowIndices a b := by
  simp [mem_xiHeightWindowIndices, hp]

example {a b : ℝ} {p : RiemannXiDivisorZeroIndex} (hb : 0 < b) (hab : a < b)
    (hp : (riemannXiDivisorZeroValue p).im = b) : p ∈ xiHeightWindowIndices a b := by
  simp [mem_xiHeightWindowIndices, hp, hb, hab]

example (a : ℝ) : xiHeightWindowIndices a a = ∅ := by
  classical
  ext p
  simp only [mem_xiHeightWindowIndices, Finset.notMem_empty, iff_false]
  rintro ⟨hp, hpa⟩
  exact (not_lt_of_ge hp.2) hpa

example : xiZeroCount 0 = 0 := by
  unfold xiZeroCount
  apply Finset.card_eq_zero.mpr
  ext p
  simp [mem_xiPositiveHeightIndices]

example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ((xiHeightWindowIndices a b).card : ℝ) -
        (∫ x in Icc a b, (1 / (2 * π)) * Real.log (x / (2 * π))) =
      xiZeroCountingRemainder b - xiZeroCountingRemainder a := by
  have h := sum_xi_height_window_sub_main_eq_remainder ha hab
    (f := fun _ => (1 : ℝ)) (g := fun _ => (0 : ℝ))
    (fun x _ => hasDerivAt_const x 1) (by simp)
  simpa using h

end

end PrimeFactorUnimodality.Tests
