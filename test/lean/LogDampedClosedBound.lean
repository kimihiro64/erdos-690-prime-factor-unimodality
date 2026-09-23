import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedBound

/-! # Power majorants and exact integrals, including cutoffs and signed densities -/

namespace Real.Tests

open Filter MeasureTheory Set
open scoped Topology

example {a q p t : ℝ} (ht : 0 < t) :
    logDampedPower a q t = t ^ (-p) * logDampedPower a (q - p) t :=
  logDampedPower_split ht

example {a q p u t : ℝ} (ha : 0 ≤ a) (hpq : p < q) (hu : 1 < u) (hut : u ≤ t) :
    logDampedPower a q t ≤ t ^ (-p) * logDampedPowerMajorant a q p u :=
  logDampedPower_le_rpow_mul_majorant ha hpq hu hut

example {a q p u : ℝ} (ha : 0 ≤ a) (hpq : p < q) (hu : 1 < u) :
    logDampedPower a q u ≤ u ^ (-p) * logDampedPowerMajorant a q p u :=
  logDampedPower_le_rpow_mul_majorant ha hpq hu le_rfl

example {a q p u : ℝ} (hw : exp (sqrt (a / (q - p))) ≤ u) :
    logDampedPowerMajorant a q p u = logDampedPower a (q - p) u := by
  simp only [logDampedPowerMajorant, ite_eq_left hw]

example {a q p u : ℝ} (hw : u < exp (sqrt (a / (q - p)))) :
    logDampedPowerMajorant a q p u = exp (-2 * sqrt (a * (q - p))) := by
  simp only [logDampedPowerMajorant, ite_eq_right (not_le.mpr hw)]

example (a q p : ℝ) :
    logDampedPowerMajorant a q p (exp (sqrt (a / (q - p)))) =
      logDampedPower a (q - p) (exp (sqrt (a / (q - p)))) := by
  simp only [logDampedPowerMajorant, le_refl, ite_true]

example {a q u : ℝ} (ha : 0 ≤ a) (hu : 1 < u) :
    logDampedPowerMajorant a q q u ≤ 1 := by
  simpa using logDampedPowerMajorant_le_peak ha (le_refl q) hu

example (a q p u : ℝ) : 0 < logDampedPowerMajorant a q p u :=
  logDampedPowerMajorant_pos a q p u

example {p q u t : ℝ} (hpq : p < q) (hu : 1 < u) (hut : u ≤ t) :
    logDampedPower 0 q t ≤ t ^ (-p) * logDampedPowerMajorant 0 q p u :=
  logDampedPower_le_rpow_mul_majorant le_rfl hpq hu hut

example {a u t : ℝ} (ha : 0 ≤ a) (hu : 1 < u) (hut : u ≤ t) :
    logDampedPower a 2 t ≤ t ^ (-(3 / 2 : ℝ)) * logDampedPowerMajorant a 2 (3 / 2) u :=
  logDampedPower_le_rpow_mul_majorant ha (by norm_num) hu hut

example {p c t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    HasDerivAt (logPowerTailPrimitive p c) ((log t - c) * t ^ (-p)) t :=
  hasDerivAt_logPowerTailPrimitive hp ht

example (c : ℝ) {p : ℝ} (hp : 1 < p) :
    Tendsto (logPowerTailPrimitive p c) atTop (𝓝 0) :=
  tendsto_logPowerTailPrimitive c hp

example {p u : ℝ} (hp : 1 < p) (hu : 0 < u) (c : ℝ) :
    IntegrableOn (fun t => (log t - c) * t ^ (-p)) (Ioi u) :=
  integrableOn_log_sub_mul_rpow_tail hp hu c

example {p u : ℝ} (hp : 1 < p) (hu : 0 < u) (c : ℝ) :
    (∫ t in Ioi u, (log t - c) * t ^ (-p)) =
      u ^ (1 - p) * ((log u - c) / (p - 1) + 1 / (p - 1) ^ 2) :=
  integral_log_sub_mul_rpow_tail hp hu c

example : (∫ t : ℝ in Ioi 1, (log t - 3) * t ^ (-(2 : ℝ))) = -2 := by
  convert integral_log_sub_mul_rpow_tail (p := 2) (u := 1) (by norm_num) (by norm_num) 3 using 1
  norm_num

example : (∫ t : ℝ in Ioi 1, (log t - (-3)) * t ^ (-(2 : ℝ))) = 4 := by
  convert integral_log_sub_mul_rpow_tail (p := 2) (u := 1)
    (by norm_num) (by norm_num) (-3) using 1
  norm_num

example {p u : ℝ} (hp : 0 < p) (hu : 0 < u) :
    (∫ t : ℝ in Ioi u, t ^ (-p) / t) = u ^ (-p) / p :=
  integral_rpow_div_tail hp hu

example {p b u : ℝ} (hp : 1 < p) (hb : 0 < b) (hu : 0 < u) :
    (∫ t in Ioi u, ((1 / b) * log (t / b)) * t ^ (-p)) +
        (∫ t in Ioi u, t ^ (-p) / t) = logDampedPowerIntegralFactor p b u :=
  integral_log_density_rpow_add_div hp hb hu

-- The identity also holds below the density scale, where the logarithm can be negative.
example : (∫ t : ℝ in Ioi 1, ((1 / 2) * log (t / 2)) * t ^ (-(2 : ℝ))) +
    (∫ t : ℝ in Ioi 1, t ^ (-(2 : ℝ)) / t) = logDampedPowerIntegralFactor 2 2 1 :=
  integral_log_density_rpow_add_div (by norm_num) (by norm_num) (by norm_num)

example {a q p b u : ℝ} (hu : 0 < u) :
    logDampedPower a (q - p) u * logDampedPowerIntegralFactor p b u =
      logDampedPower a q u *
        ((u / b) * (log (u / b) / (p - 1) + 1 / (p - 1) ^ 2) + 1 / p) :=
  logDampedPower_mul_integralFactor hu

example {p b u : ℝ} (hp : 1 < p) (hb : 0 < b) (hbu : b ≤ u) :
    0 ≤ logDampedPowerIntegralFactor p b u :=
  logDampedPowerIntegralFactor_nonneg hp hb hbu

example {a q p b u C : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hp : 1 < p) (hb : 0 < b) (hu : 1 < u) (hbu : b ≤ u)
    (hbound : ∀ t ∈ Ici u, logDampedPower a q t ≤ t ^ (-p) * C) :
    (∫ t in Ioi u, ((1 / b) * log (t / b)) * logDampedPower a q t) +
        (∫ t in Ioi u, logDampedPower a q t / t) ≤
      C * logDampedPowerIntegralFactor p b u :=
  integral_logDampedPower_density_le_of_majorant ha hq hp hb hu hbu hbound

end Real.Tests
