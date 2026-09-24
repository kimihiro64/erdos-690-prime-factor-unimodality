/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

/-! # Explicit bounds for tails dominated by a real power

The integral test supplies the exact cutoff factor. The normed-space
version proves convergence as well as the bound, so it cannot use the
default value of a divergent infinite sum.
-/

open MeasureTheory Set

namespace Real

/-- The full positive tail of a real power, starting strictly after `J`. -/
theorem tsum_nat_rpow_tail_le {p : ℝ} (hp : 1 < p) {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℕ, ((n + J + 1 : ℕ) : ℝ) ^ (-p)) ≤ (J : ℝ) ^ (1 - p) / (p - 1) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have ha : AntitoneOn (fun x : ℝ => x ^ (-p)) (Ici (J : ℝ)) :=
    (antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
      (fun _ hx => hJr.trans_le hx)
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) hJr
  have ht := ha.tsum_comp_add_le_integral J hi (fun x hx => rpow_nonneg (hJr.trans hx).le _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -p < -1) hJr] at ht
  convert ht using 1
  rw [show -p + 1 = 1 - p by ring]
  have he : 1 - p = -(p - 1) := by ring
  rw [he, div_neg, neg_div, neg_neg]

/-- Every shifted real-power tail converges for exponent strictly below minus one. -/
theorem summable_nat_rpow_tail {p : ℝ} (hp : 1 < p) (J : ℕ) :
    Summable (fun n : ℕ => ((n + J + 1 : ℕ) : ℝ) ^ (-p)) := by
  have hs := (summable_nat_rpow.mpr (by linarith : -p < -1))
  simpa only [Nat.add_assoc] using (summable_nat_add_iff (J + 1)).mpr hs

end Real

variable {E : Type*} [NormedAddCommGroup E]

/-- Domination by a convergent power tail proves convergence of the actual terms. -/
theorem summable_of_norm_le_rpow_tail [CompleteSpace E] {f : ℕ → E} {C p : ℝ} {J : ℕ}
    (hp : 1 < p) (hf : ∀ n, ‖f n‖ ≤ C * ((n + J + 1 : ℕ) : ℝ) ^ (-p)) :
    Summable f :=
  ((Real.summable_nat_rpow_tail hp J).mul_left C).of_norm_bounded hf

/-- The complete normed tail retains the cutoff and the denominator `p-1`. -/
theorem norm_tsum_le_rpow_tail {f : ℕ → E} {C p : ℝ} {J : ℕ}
    (hC : 0 ≤ C) (hp : 1 < p) (hJ : 0 < J)
    (hf : ∀ n, ‖f n‖ ≤ C * ((n + J + 1 : ℕ) : ℝ) ^ (-p)) :
    ‖∑' n : ℕ, f n‖ ≤ C * ((J : ℝ) ^ (1 - p) / (p - 1)) := by
  have ht := tsum_of_norm_bounded ((Real.summable_nat_rpow_tail hp J).hasSum.mul_left C) hf
  exact ht.trans (mul_le_mul_of_nonneg_left (Real.tsum_nat_rpow_tail_le hp hJ) hC)
