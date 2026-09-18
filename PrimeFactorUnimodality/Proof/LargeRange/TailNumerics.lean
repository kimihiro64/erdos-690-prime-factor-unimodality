import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum.Prime
import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Exact logarithmic anchors for the optimized tail cutoff -/

namespace PrimeFactorUnimodality

noncomputable section

/-- A rational lower bound for the logarithm of the proposed optimized
uniform-tail cutoff.  The integer comparison was chosen so that only
Mathlib's certified bounds for `log 2` and `log 3` are needed. -/
theorem log_38000_gt : (1054 : Real) / 100 < Real.log 38000 := by
  have power_lt : (2 : Real) ^ 6 * 3 ^ 25 < 38000 ^ 3 := by norm_num
  have logged := Real.log_lt_log (by positivity) power_lt
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow,
    Real.log_pow, Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

/-- A matching rational upper bound for `log 38000`. -/
theorem log_38000_lt : Real.log 38000 < (264 : Real) / 25 := by
  have power_lt : (38000 : Real) ^ 3 < 2 ^ 14 * 3 ^ 20 := by norm_num
  have logged := Real.log_lt_log (by positivity) power_lt
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow,
    Real.log_pow, Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

theorem log_nat_gt_1054_div_100 {r : Nat} (hr : 38000 ≤ r) :
    (1054 : Real) / 100 < Real.log r := by
  exact log_38000_gt.trans_le
    (Real.log_le_log (by norm_num) (by exact_mod_cast hr))

/-- The elementary cutoff function `x / log x` is monotone once `x ≥ 3`.
This isolates the calculus argument used to propagate a single checked
endpoint inequality through the whole uniform tail. -/
theorem div_log_monotoneOn_three :
    MonotoneOn (fun x : Real => x / Real.log x) (Set.Ici 3) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 3)
  · exact continuousOn_id.div
      (continuousOn_id.log (by intro x hx; norm_num at hx ⊢; linarith))
      (by
        intro x hx
        exact (Real.log_pos (by norm_num at hx ⊢; linarith)).ne')
  · exact differentiableOn_id.div
      (differentiableOn_id.log (by
        intro x hx
        simp only [interior_Ici, Set.mem_Ioi] at hx
        simpa only [id_eq] using (show x ≠ 0 by linarith)))
      (by
        intro x hx
        simp only [interior_Ici, Set.mem_Ioi] at hx
        exact (Real.log_pos (by linarith)).ne')
  · intro x hx
    simp only [interior_Ici, Set.mem_Ioi] at hx
    have x_pos : 0 < x := by linarith
    have log_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have log_gt_one : 1 < Real.log x := by
      have log_three_gt : 1 < Real.log 3 :=
        (by norm_num : (1 : Real) < 1.0986122885).trans
          Real.log_three_gt_d9
      exact log_three_gt.trans_le (Real.log_le_log (by norm_num) hx.le)
    rw [deriv_fun_div (by fun_prop) (Real.differentiableAt_log x_pos.ne')
      log_pos.ne', deriv_id'', Real.deriv_log]
    simp only [one_mul, mul_inv_cancel₀ x_pos.ne']
    exact div_nonneg (by linarith) (sq_nonneg _)

theorem tailScale_38000_gt :
    (3500 : Real) < (491 / 500 : Real) * 38000 / Real.log 38000 := by
  have log_pos : 0 < Real.log (38000 : Real) := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ log_pos]
  nlinarith [log_38000_lt]

/-- The scale `0.99 r / log r` stays above the short-interval threshold
throughout the optimized tail. -/
theorem tailScale_gt_3500 {r : Nat} (hr : 38000 ≤ r) :
    (3500 : Real) < (491 / 500 : Real) * r / Real.log r := by
  have r_three : (3 : Real) ≤ r := by exact_mod_cast (show 3 ≤ r by omega)
  have cutoff_le : (38000 : Real) ≤ r := by exact_mod_cast hr
  have ratioMono := div_log_monotoneOn_three (by norm_num) r_three cutoff_le
  have factor_pos : (0 : Real) < 491 / 500 := by norm_num
  exact tailScale_38000_gt.trans_le
    (by
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left ratioMono factor_pos.le)

/-- The fixed prime `3301` places the predecessor of the selected prime in
Dusart's valid range even though half of the optimized scale is below `3275`.
-/
theorem exists_tail_consecutive_primes
    (shortInterval : HasDusartShortIntervalPrime) {r : Nat} (hr : 38000 ≤ r) :
    ∃ qPrev q : Nat,
      ConsecutivePrimes qPrev q ∧ 3301 ≤ qPrev ∧
      (491 / 500 : Real) * r / Real.log r < q ∧
      (q : Real) ≤
        ((491 / 500 : Real) * r / Real.log r) *
          (1 + 1 /
            (2 * (Real.log ((491 / 500 : Real) * r / Real.log r)) ^ 2)) ∧
      (491 / 500 : Real) * r / Real.log r <
        qPrev * (1 + 1 / (2 * (Real.log qPrev) ^ 2)) := by
  have scale_gt := tailScale_gt_3500 hr
  apply exists_consecutive_primes_above_fixed shortInterval
    (x := (491 / 500 : Real) * r / Real.log r) (s := 3301)
  · linarith
  · norm_num
  · norm_num
  · linarith

end

end PrimeFactorUnimodality
