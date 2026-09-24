import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxReflectedTail
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserClosedBounds

/-! # A reflected high-tail bound frozen at one starting point

The region term decreases with the logarithmic base point; so does the
critical-line term. The same elementary half-sum therefore bounds the
entire later ray. Fixing the relative step cancels the arithmetic scale.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The complete closed reflected tail, with the other half's power cost retained. -/
def dusartReflectedClosedTail (b R q p H : ℝ) : ℝ :=
  (xiRosserClosedTailBound (b / R) q p H +
    exp (-(1 / 2) * b) * xiRosserPowerTailBound q H) / 2

/-- A starting-point reflected majorant bounds every later actual high-zero sum. -/
theorem norm_dusartBoxXiHighSum_le_reflected_frozen (m : ℕ) {h x x₀ R p T : ℝ}
    (hh : 0 < h) (hx₀ : 1 < x₀) (hx : x₀ ≤ x) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ)) (hT : 10 < T)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    ‖dusartBoxXiHighSum m h x T‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        dusartReflectedClosedTail (Real.log x₀) R (m + 4 : ℕ) p T := by
  have hx1 := hx₀.trans_le hx
  have hxpos := lt_trans zero_lt_one hx1
  have ha : 0 ≤ Real.log x₀ / R := div_nonneg (Real.log_pos hx₀).le hR.le
  have hq : (2 : ℝ) ≤ (m + 4 : ℕ) := by norm_cast; omega
  have hlog := Real.log_le_log (lt_trans zero_lt_one hx₀) hx
  have hd := (xiRosserAbsoluteTail_antitone_parameter ha
    (div_le_div_of_nonneg_right hlog hR.le) hq (by linarith : 1 < T)).trans
    (xiRosserAbsoluteTail_le_closed ha hq hp hpq hT hpeak)
  have he : exp (-(1 / 2) * Real.log x) ≤ exp (-(1 / 2) * Real.log x₀) := by
    apply exp_le_exp.mpr
    linarith
  have hu := xiRosserAbsoluteTail_zero_le_power hq hT
  have hu0 : 0 ≤ xiRosserAbsoluteTail 0 (m + 4 : ℕ) T :=
    tsum_nonneg (fun _ => (logDampedPower_pos _ _ _).le)
  have hr := mul_le_mul he hu hu0 (exp_pos _).le
  exact (norm_dusartBoxXiHighSum_le_reflected_tail m hh hx1 hR (by linarith) hreg).trans
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (add_le_add hd hr) (by norm_num))
      (by positivity))

/-- A fixed relative step makes the reflected normalized majorant constant along the ray. -/
theorem norm_dusartBoxXiHighSum_div_le_reflected_frozen (m : ℕ) {s x x₀ R p T : ℝ}
    (hs : 0 < s) (hx₀ : 1 < x₀) (hx : x₀ ≤ x) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ)) (hT : 10 < T)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    ‖dusartBoxXiHighSum m (s * x) x T‖ / x ≤
      (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
        dusartReflectedClosedTail (Real.log x₀) R (m + 4 : ℕ) p T := by
  have hxpos : 0 < x := (lt_trans zero_lt_one hx₀).trans_le hx
  have ht := norm_dusartBoxXiHighSum_le_reflected_frozen m (mul_pos hs hxpos)
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
