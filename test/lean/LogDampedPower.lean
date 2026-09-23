import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDampedShape

/-! # Damped-power derivative, maximum and degenerate-parameter regressions -/

open Real Set

example (t : ℝ) : logDampedPower 0 0 t = 1 := by simp [logDampedPower]

example {q t : ℝ} (ht : 0 < t) : logDampedPower 0 q t = t ^ (-q) := by
  simp [logDampedPower_eq_rpow_mul ht]

example (a q t : ℝ) : 0 < logDampedPower a q t := logDampedPower_pos a q t

example {a q t : ℝ} (ht : 1 < t) :
    HasDerivAt (logDampedPower a q) (logDampedPowerSlope a q t) t :=
  hasDerivAt_logDampedPower ht

example {a q t : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (ht : 1 < t) :
    logDampedPower a q t ≤ exp (-2 * sqrt (a * q)) :=
  logDampedPower_le_exp_sqrt ha hq ht

example {a q : ℝ} (ha : 0 ≤ a) (hq : 0 < q) (hw : 1 < exp (sqrt (a / q))) :
    logDampedPowerSlope a q (exp (sqrt (a / q))) = 0 :=
  le_antisymm (logDampedPowerSlope_nonpos_after ha hq hw le_rfl)
    (logDampedPowerSlope_nonneg_before ha hq hw le_rfl)

example {q t : ℝ} (hq : 0 < q) (ht : 1 < t) : logDampedPowerSlope 0 q t ≤ 0 := by
  apply logDampedPowerSlope_nonpos_after le_rfl hq ht
  simpa using ht.le

example {a q u v : ℝ} (hu : 1 < u) :
    ContinuousOn (logDampedPowerSlope a q) (Icc u v) :=
  continuousOn_logDampedPowerSlope (fun _ ht => hu.trans_le ht.1)

example {a q : ℝ} {D : Set ℝ} (hD : Convex ℝ D)
    (ht : ∀ t ∈ D, 1 < t) (hreg : ∀ t ∈ D, q * log t ^ 2 ≤ a) :
    MonotoneOn (logDampedPower a q) D := logDampedPower_monotoneOn hD ht hreg

example {a q : ℝ} {D : Set ℝ} (hD : Convex ℝ D)
    (ht : ∀ t ∈ D, 1 < t) (hreg : ∀ t ∈ D, a ≤ q * log t ^ 2) :
    AntitoneOn (logDampedPower a q) D := logDampedPower_antitoneOn hD ht hreg
