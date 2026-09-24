import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxReflectedAverage
import PrimeFactorUnimodality.Helpers.Analytic.DusartPsiRelativeAverages

/-! # The reflected high tail gives an actual pointwise psi bound

Evaluate both adjacent averages at their own frozen reference point. Their
exact rescaling and the full smoothing loss remain in the pointwise bound,
which applies to every real point on the ray, including prime-power jumps.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

/-- Both reflected reference averages and their complete smoothing allowance. -/
def dusartReflectedFrozenPsiBound (m : ℕ) (s x₀ R p a H δ : ℝ) : ℝ :=
  let t := 1 - (m + 3 : ℕ) * s
  max (t * dusartReflectedRelativeBudget m (s / t) (x₀ * t) R p a H δ)
    (dusartReflectedRelativeBudget m s x₀ R p a H δ) + (m + 3 : ℕ) * s / 2

/-- Reflection improves the complete pointwise estimate, not merely a formal scalar expression. -/
theorem abs_psi_sub_div_le_reflected_frozen (m : ℕ) {s x x₀ R p a H δ : ℝ}
    (hs : 0 < s) (hx₀ : 0 < x₀) (hx : x₀ ≤ x)
    (hl₀ : 1 < x₀ * (1 - (m + 3 : ℕ) * s)) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤ dusartReflectedFrozenPsiBound m s x₀ R p a H δ := by
  let t := 1 - (m + 3 : ℕ) * s
  have ht : 0 < t := (mul_pos_iff_of_pos_left hx₀).mp (lt_trans zero_lt_one hl₀)
  have ht1 : t ≤ 1 := sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hs.le)
  have hlx₀ : x₀ * t ≤ x₀ := by nlinarith
  have hx₀1 : 1 < x₀ := hl₀.trans_le hlx₀
  have hxpos : 0 < x := hx₀.trans_le hx
  have hleft : x₀ * t ≤ x * t := mul_le_mul_of_nonneg_right hx ht.le
  have hleftpos : 0 < x * t := mul_pos hxpos ht
  have hpeak₀ : exp (sqrt ((Real.log (x₀ * t) / R) / (m + 4 : ℕ))) ≤ H :=
    (Real.exp_le_exp.mpr (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right
        (Real.log_le_log (mul_pos hx₀ ht) hlx₀) hR.le) (Nat.cast_nonneg _)))).trans hpeak
  have hl := abs_dusartPsiAverageError_div_le_reflected_frozen m (div_pos hs ht) hl₀ hleft
    hR hp hpq ha haH hδ hgap hpeak₀ hreg
  have hstep : (s / t) * (x * t) = s * x := by field_simp
  rw [hstep] at hl
  exact dusart_abs_psi_div_le_of_relative_averages (m + 3) hs hxpos hleftpos hl
    (abs_dusartPsiAverageError_div_le_reflected_frozen m hs hx₀1 hx hR hp hpq
      ha haH hδ hgap hpeak hreg)

end

end PrimeFactorUnimodality
