/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Cubic exponential majorants from a single endpoint

The exponential series has nonnegative coefficients. After its quadratic
part is removed, comparison of the remaining powers controls the cubic
remainder uniformly on a nonnegative interval by its right endpoint.
The proof reuses Mathlib's exponential series and summable order API.
-/

namespace Real

/-- The cubic-normalized exponential remainder increases on the nonnegative axis. -/
theorem exp_cubic_remainder_mul_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    y ^ 3 * (exp x - 1 - x - x ^ 2 / 2) ≤
      x ^ 3 * (exp y - 1 - y - y ^ 2 / 2) := by
  have ht (v : ℝ) : HasSum (fun n : ℕ => v ^ (n + 3) / (n + 3).factorial)
      (exp v - 1 - v - v ^ 2 / 2) := by
    have he : HasSum (fun n : ℕ => v ^ n / n.factorial) (exp v) := by
      simpa only [exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp v
    have h := (hasSum_nat_add_iff' 3).mpr he
    norm_num [Finset.sum_range_succ] at h
    convert h using 1
    ring
  apply hasSum_le (f := fun n : ℕ => y ^ 3 * (x ^ (n + 3) / (n + 3).factorial))
    (g := fun n : ℕ => x ^ 3 * (y ^ (n + 3) / (n + 3).factorial)) _
    ((ht x).mul_left (y ^ 3)) ((ht y).mul_left (x ^ 3))
  intro n
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy n)
    (mul_nonneg (pow_nonneg hx 3) (pow_nonneg (hx.trans hxy) 3))
  have hd := div_le_div_of_nonneg_right hp (Nat.cast_nonneg (n + 3).factorial)
  convert hd using 1 <;> rw [pow_add] <;> ring

/-- One endpoint exponential inequality certifies the whole cubic majorant interval. -/
theorem exp_le_cubic_of_endpoint {x y C : ℝ} (hy : 0 < y) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hend : exp y ≤ 1 + y + y ^ 2 / 2 + C * y ^ 3) :
    exp x ≤ 1 + x + x ^ 2 / 2 + C * x ^ 3 := by
  have h := exp_cubic_remainder_mul_le hx hxy
  have hb := mul_le_mul_of_nonneg_left hend (pow_nonneg hx 3)
  apply (mul_le_mul_iff_right₀ (pow_pos hy 3)).mp
  nlinarith only [h, hb]

end Real
