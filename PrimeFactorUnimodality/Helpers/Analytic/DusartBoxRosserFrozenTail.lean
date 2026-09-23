import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserClosedTail

/-! # A fixed starting-point estimate for the complete high-zero tail

Increasing the arithmetic base point increases damping at every zero.
Evaluate the closed majorant once at the starting point and retain it
throughout the entire ray. The turning-point condition is needed only
there, not again at each larger base point. With a fixed relative step,
the normalized bound is independent of the running base point.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- One admissible starting-point majorant controls every later high-zero sum. -/
theorem norm_dusartBoxXiHighSum_le_frozen_closed (m : ℕ) {h x x₀ R p T : ℝ}
    (hh : 0 < h) (hx₀ : 1 < x₀) (hx : x₀ ≤ x) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ)) (hT : 10 < T)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    ‖dusartBoxXiHighSum m h x T‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        xiRosserClosedTailBound (Real.log x₀ / R) (m + 4 : ℕ) p T := by
  have ha : 0 ≤ Real.log x₀ / R := div_nonneg (Real.log_pos hx₀).le hR.le
  have hq : (2 : ℝ) ≤ (m + 4 : ℕ) := by norm_cast; omega
  have hab := div_le_div_of_nonneg_right
    (Real.log_le_log (lt_trans zero_lt_one hx₀) hx) hR.le
  have ht := (xiRosserAbsoluteTail_antitone_parameter ha hab hq (by linarith : 1 < T)).trans
    (xiRosserAbsoluteTail_le_closed ha hq hp hpq hT hpeak)
  have hxpos : 0 < x := (lt_trans zero_lt_one hx₀).trans_le hx
  exact (norm_dusartBoxXiHighSum_le_actual_tail m hh (hx₀.trans_le hx) hR
    (by linarith) hreg).trans (mul_le_mul_of_nonneg_left ht (by positivity))


/-- Fixing the relative step makes the complete normalized tail bound constant on the ray. -/
theorem norm_dusartBoxXiHighSum_div_le_frozen_closed (m : ℕ) {s x x₀ R p T : ℝ}
    (hs : 0 < s) (hx₀ : 1 < x₀) (hx : x₀ ≤ x) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ)) (hT : 10 < T)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    ‖dusartBoxXiHighSum m (s * x) x T‖ / x ≤
      (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
        xiRosserClosedTailBound (Real.log x₀ / R) (m + 4 : ℕ) p T := by
  have hxpos : 0 < x := (lt_trans zero_lt_one hx₀).trans_le hx
  have ht := norm_dusartBoxXiHighSum_le_frozen_closed m (mul_pos hs hxpos)
    hx₀ hx hR hp hpq hT hpeak hreg
  have hU : x + (m + 3 : ℕ) * (s * x) = x * (1 + (m + 3 : ℕ) * s) := by ring
  have hC : 2 ^ (m + 3) * (x * (1 + (m + 3 : ℕ) * s)) ^ (m + 4) /
      (s * x) ^ (m + 3) =
      x * (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) := by
    rw [mul_pow, mul_pow, show m + 4 = (m + 3) + 1 by omega, pow_succ x]
    field_simp
  rw [hU, hC] at ht
  apply (div_le_iff₀ hxpos).mpr
  convert ht using 1
  ring


end

end PrimeFactorUnimodality
