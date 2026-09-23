import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedSharpTail

/-! # Regression tests for sharp Rosser tail estimates -/

namespace Real.Tests

open MeasureTheory Set

example {a m b u t : ℝ} (hm : 0 < m) (hu : 1 < u)
    (hgap : a < m * log u ^ 2) (hut : u ≤ t)
    (hparam : log b ≤ 1 / m + sqrt (a / m)) : 0 ≤ logDampedTailPrimitive a m b t :=
  logDampedTailPrimitive_nonneg hm hu hgap hut hparam

example {a m b u v : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hb : 0 < b) (hu : 1 < u) (huv : u ≤ v)
    (hgap : a < m * log u ^ 2) (hparam : log b ≤ 1 / m + sqrt (a / m)) :
    (∫ t in Icc u v, log (t / b) * logDampedPower a (m + 1) t) ≤
      logDampedTailPrimitive a m b u - logDampedTailPrimitive a m b v :=
  integral_logDampedPower_log_le_sub ha hm hb hu huv hgap hparam

example {a m b u : ℝ}
    (ha : 0 ≤ a) (hm : 1 ≤ m) (hb : 0 < b) (hu : 1 < u)
    (hgap : a < m * log u ^ 2) (hparam : log b ≤ 1 / m + sqrt (a / m)) :
    (∫ t in Ioi u, log (t / b) * logDampedPower a (m + 1) t) ≤
      logDampedTailPrimitive a m b u :=
  integral_logDampedPower_log_tail_le ha hm hb hu hgap hparam

example {m ν X b : ℝ} (hX : 0 < X) (hν : 0 < ν) :
    logDampedTailPrimitive (X ^ 2) m b (exp (ν * X)) =
      exp (-m * (ν * X) - X / ν) * (ν ^ 2 / (m * ν ^ 2 - 1)) *
        (ν * X + 1 / m - log b) :=
  logDampedTailPrimitive_exp hX hν

-- The reciprocal correction only needs a positive power, not a power above one.
example {a q p u C : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (hp : 0 < p) (hu : 1 < u)
    (hbound : ∀ t ∈ Ici u, logDampedPower a q t ≤ t ^ (-p) * C) :
    (∫ t in Ioi u, logDampedPower a q t / t) ≤ C * (u ^ (-p) / p) :=
  integral_logDampedPower_div_le_of_majorant ha hq hp hu hbound

example {a q p u : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (hp : 0 < p) (hpq : p < q)
    (hu : 1 < u) (hw : exp (sqrt (a / (q - p))) ≤ u) :
    (∫ t in Ioi u, logDampedPower a q t / t) ≤ logDampedPower a q u / p :=
  integral_logDampedPower_div_le_cutoff ha hq hp hpq hu hw

-- The endpoint integrability case m=1 and zero damping are supported.
example : (∫ t in Ioi (exp 1), log (t / 1) * logDampedPower 0 2 t) ≤
    logDampedTailPrimitive 0 1 1 (exp 1) := by
  have h := integral_logDampedPower_log_tail_le (a := 0) (m := 1) (b := 1)
    (u := exp 1) (by norm_num) (by norm_num) (by norm_num)
    (one_lt_exp_iff.mpr (by norm_num)) (by simp) (by norm_num)
  norm_num at h ⊢
  exact h

-- Equality at the auxiliary parameter bound is allowed.
example {a m u : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m) (hu : 1 < u)
    (hgap : a < m * log u ^ 2) :
    (∫ t in Ioi u, log (t / exp (1 / m + sqrt (a / m))) * logDampedPower a (m + 1) t) ≤
      logDampedTailPrimitive a m (exp (1 / m + sqrt (a / m))) u :=
  integral_logDampedPower_log_tail_le ha hm (exp_pos _) hu hgap (by rw [log_exp])

-- A degenerate finite interval gives a zero endpoint difference.
example {a m b u : ℝ} (ha : 0 ≤ a) (hm : 0 < m) (hb : 0 < b) (hu : 1 < u)
    (hgap : a < m * log u ^ 2) (hparam : log b ≤ 1 / m + sqrt (a / m)) :
    (∫ t in Icc u u, log (t / b) * logDampedPower a (m + 1) t) ≤ 0 := by
  simpa only [sub_self] using integral_logDampedPower_log_le_sub ha hm hb hu le_rfl hgap hparam

example {X m b : ℝ} (hX : 0 ≤ X) (hm : 0 < m) :
    log b ≤ 1 / m + sqrt (X ^ 2 / m) ↔ (m * log b - 1) / sqrt m ≤ X :=
  logDampedTail_parameter_iff hX hm

example {m ν L : ℝ} (hν : 0 < ν) (hmargin : 1 < m * ν ^ 2) :
    (ν ^ 2 / (m * ν ^ 2 - 1)) * (L + 1 / m) ≤
      L / (m - 1 / ν ^ 2) + 1 / (m - 1 / ν ^ 2) ^ 2 :=
  logDampedTail_factor_le_power hν hmargin

-- The parameter equivalence includes a zero root and equality at the boundary.
example : log (exp 1) ≤ 1 / (1 : ℝ) + sqrt (0 ^ 2 / 1) ↔
    ((1 : ℝ) * log (exp 1) - 1) / sqrt 1 ≤ 0 :=
  logDampedTail_parameter_iff (by norm_num) (by norm_num)

-- The comparison does not require the logarithmic offset to be positive.
example : ((1 : ℝ) ^ 2 / (3 * 1 ^ 2 - 1)) * (-2 + 1 / 3) ≤
    -2 / (3 - 1 / 1 ^ 2) + 1 / (3 - 1 / 1 ^ 2) ^ 2 :=
  logDampedTail_factor_le_power (by norm_num) (by norm_num)

end Real.Tests
