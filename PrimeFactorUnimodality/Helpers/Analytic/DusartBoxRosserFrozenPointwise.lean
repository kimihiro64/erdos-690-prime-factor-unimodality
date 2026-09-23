import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserFrozenAverage
import PrimeFactorUnimodality.Helpers.Analytic.DusartPsiRelativeAverages

/-! # One elementary endpoint value controls a whole psi ray

Both adjacent averages use the same fixed relative smoothing width.
Their reference points are the two corresponding points at the start
of the ray. Monotonicity of the actual damped tails, low terms and
corrections makes the resulting pointwise budget independent of the
running base point. This supplies the uniformity needed for the paper's
tables of relative errors, including prime-power discontinuities.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

/-- The relative error budget evaluated only at the two initial arithmetic points. -/
def dusartRosserFrozenPsiBound (m : ℕ) (s x₀ R p a H δ : ℝ) : ℝ :=
  let t := 1 - (m + 3 : ℕ) * s
  max (t * dusartBoxRosserFixedRelativeBudget m (s / t) (x₀ * t) R p a H δ)
    (dusartBoxRosserFixedRelativeBudget m s x₀ R p a H δ) + (m + 3 : ℕ) * s / 2

/-- The initial endpoint budget bounds the actual relative psi error on the entire ray. -/
theorem abs_psi_sub_div_le_frozen (m : ℕ) {s x x₀ R p a H δ : ℝ}
    (hs : 0 < s) (hx₀ : 0 < x₀) (hx : x₀ ≤ x)
    (hl₀ : 1 < x₀ * (1 - (m + 3 : ℕ) * s)) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤ dusartRosserFrozenPsiBound m s x₀ R p a H δ := by
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
  have hl := abs_dusartPsiAverageError_div_le_frozen m (div_pos hs ht) hl₀ hleft
    hR hp hpq ha haH hδ hgap hpeak₀ hreg
  have hstep : (s / t) * (x * t) = s * x := by field_simp
  rw [hstep] at hl
  exact dusart_abs_psi_div_le_of_relative_averages (m + 3) hs hxpos hleftpos hl
    (abs_dusartPsiAverageError_div_le_frozen m hs hx₀1 hx hR hp hpq ha haH hδ hgap hpeak hreg)

end

end PrimeFactorUnimodality
