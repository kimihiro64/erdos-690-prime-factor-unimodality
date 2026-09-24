import PrimeFactorUnimodality.Mathlib.Analysis.PSeries.TailBound

/-! Power-tail cutoffs retain their exact exponent and denominator and prove convergence. -/

example {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℕ, ((n + J + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))) ≤ (J : ℝ) ^ (-1 : ℝ) := by
  convert Real.tsum_nat_rpow_tail_le (p := 2) (by norm_num) hJ using 1
  norm_num

example {J : ℕ} (hJ : 0 < J) {f : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C * ((n + J + 1 : ℕ) : ℝ) ^ (-(3 : ℝ))) :
    ‖∑' n, f n‖ ≤ C * ((J : ℝ) ^ (-(2 : ℝ)) / 2) := by
  convert norm_tsum_le_rpow_tail hC (by norm_num : (1 : ℝ) < 3) hJ hf using 1
  norm_num

example {f : ℕ → ℂ} {C : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ C * ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))) : Summable f := by
  exact summable_of_norm_le_rpow_tail (J := 0) (by norm_num : (1 : ℝ) < 2) hf
