import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDamped

/-! # Decay and absolute integrability of the damped tail, including exponent two -/

open Real Filter MeasureTheory Set
open scoped Topology

example {a q t : ℝ} (ha : 0 ≤ a) (ht : 1 < t) : logDampedPower a q t ≤ t ^ (-q) :=
  logDampedPower_le_rpow ha ht

example {a t : ℝ} (ha : 0 ≤ a) (ht : 1 < t) : logDampedPower a 2 t ≤ 1 / t ^ 2 :=
  logDampedPower_le_inv_sq ha le_rfl ht

example : Tendsto (logDampedPower 0 2) atTop (𝓝 0) :=
  tendsto_logDampedPower_atTop le_rfl le_rfl

example {a q u : ℝ} (ha : 0 ≤ a) (hq : 0 < q) (hu : 1 < u)
    (hw : exp (sqrt (a / q)) ≤ u) : AntitoneOn (logDampedPower a q) (Ioi u) :=
  antitoneOn_logDampedPower_after ha hq hu hw

example {u : ℝ} (hu : 1 < u) : IntegrableOn (fun t : ℝ => log t / t ^ 2) (Ioi u) :=
  integrableOn_log_div_sq hu

example {u : ℝ} (hu : 1 < u) : IntegrableOn (logDampedPower 0 2) (Ioi u) :=
  integrableOn_logDampedPower le_rfl le_rfl hu

example {a q u : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) :
    IntegrableOn (fun t => log t * logDampedPower a q t) (Ioi u) :=
  integrableOn_log_mul_logDampedPower ha hq hu

example {a q u : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) :
    IntegrableOn (fun t => logDampedPower a q t / t) (Ioi u) :=
  integrableOn_logDampedPower_div ha hq hu

example {a q u b : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) (hb : 0 < b) :
    IntegrableOn (fun t => log (t / b) * logDampedPower a q t) (Ioi u) :=
  integrableOn_log_div_mul_logDampedPower ha hq hu hb
