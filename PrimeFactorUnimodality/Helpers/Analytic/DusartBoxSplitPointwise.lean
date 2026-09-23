import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserFrozenPointwise
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxSplitAverage

/-! # Pointwise psi control with a split low-zero block

Apply the improved low-zero estimate to the two adjacent averages.
The resulting endpoint value controls the entire ray, including jumps.
For admissible smoothing widths it is no larger than the old value;
coincident cutoffs recover that value exactly.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

/-- The refined relative psi bound evaluated at the two initial arithmetic points. -/
def dusartRosserSplitPsiBound (m : ℕ) (s x₀ R p a U H δ : ℝ) : ℝ :=
  let t := 1 - (m + 3 : ℕ) * s
  max (t * dusartBoxRosserSplitRelativeBudget m (s / t) (x₀ * t) R p a U H δ)
    (dusartBoxRosserSplitRelativeBudget m s x₀ R p a U H δ) + (m + 3 : ℕ) * s / 2

/-- Refining the low block cannot worsen the normalized pointwise bound. -/
theorem dusartRosserSplitPsiBound_le_frozen (m : ℕ) {s x₀ R p a U H δ : ℝ}
    (hs : (m + 3 : ℕ) * s ≤ 1) :
    dusartRosserSplitPsiBound m s x₀ R p a U H δ ≤
      dusartRosserFrozenPsiBound m s x₀ R p a H δ := by
  apply add_le_add _ le_rfl
  apply max_le_max
  · exact mul_le_mul_of_nonneg_left
      (dusartBoxRosserSplitRelativeBudget_le_fixed _ _ _ _ _ _ _ _ _) (sub_nonneg.mpr hs)
  · exact dusartBoxRosserSplitRelativeBudget_le_fixed _ _ _ _ _ _ _ _ _

/-- The pointwise budget is unchanged when there is no intermediate low band. -/
@[simp] theorem dusartRosserSplitPsiBound_self (m : ℕ) (s x₀ R p a H δ : ℝ) :
    dusartRosserSplitPsiBound m s x₀ R p a H H δ =
      dusartRosserFrozenPsiBound m s x₀ R p a H δ := by
  simp only [dusartRosserSplitPsiBound, dusartBoxRosserSplitRelativeBudget_self]
  rfl

/-- A refined endpoint estimate bounds actual psi at every point of the ray. -/
theorem abs_psi_sub_div_le_split_frozen (m : ℕ) {s x x₀ R p a U H δ : ℝ}
    (hs : 0 < s) (hx₀ : 0 < x₀) (hx : x₀ ≤ x)
    (hl₀ : 1 < x₀ * (1 - (m + 3 : ℕ) * s)) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haU : a < U) (hUH : U ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤ dusartRosserSplitPsiBound m s x₀ R p a U H δ := by
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
  have hl := abs_dusartPsiAverageError_div_le_split_frozen m (div_pos hs ht) hl₀ hleft
    hR hp hpq ha haU hUH hδ hgap hpeak₀ hreg
  have hstep : (s / t) * (x * t) = s * x := by field_simp
  rw [hstep] at hl
  exact dusart_abs_psi_div_le_of_relative_averages (m + 3) hs hxpos hleftpos hl
    (abs_dusartPsiAverageError_div_le_split_frozen m hs hx₀1 hx hR hp hpq
      ha haU hUH hδ hgap hpeak hreg)

end

end PrimeFactorUnimodality
