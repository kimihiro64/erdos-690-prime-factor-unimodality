import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxLowSplit

/-! # Uniform psi averages with optimized low-zero control

The inner cutoff only changes how the same low zeros are estimated.
Take the minimum of the original and split bounds, so the refinement
never worsens the previous estimate. The high tail, corrections and
actual zero-location hypotheses are unchanged. No scalar value is assumed.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real intervalIntegral

/-- The normalized endpoint budget with the better of two low-zero estimates. -/
def dusartBoxRosserSplitRelativeBudget (m : ℕ) (s x R p a U H δ : ℝ) : ℝ :=
  min (((1 + (m + 3 : ℕ) * s) * exp (-δ * Real.log x)) * xiLowReciprocalNormBound a H δ)
    (dusartBoxSplitLowBound m s x a U H δ) +
    (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
      xiRosserClosedTailBound (Real.log x / R) (m + 4 : ℕ) p H +
    (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x

/-- Choosing a split never increases the original elementary budget. -/
theorem dusartBoxRosserSplitRelativeBudget_le_fixed (m : ℕ) (s x R p a U H δ : ℝ) :
    dusartBoxRosserSplitRelativeBudget m s x R p a U H δ ≤
      dusartBoxRosserFixedRelativeBudget m s x R p a H δ :=
  add_le_add (add_le_add (min_le_left _ _) le_rfl) le_rfl

/-- Equal inner and outer cutoffs recover the original formula exactly. -/
@[simp] theorem dusartBoxRosserSplitRelativeBudget_self (m : ℕ) (s x R p a H δ : ℝ) :
    dusartBoxRosserSplitRelativeBudget m s x R p a H H δ =
      dusartBoxRosserFixedRelativeBudget m s x R p a H δ := by
  simp only [dusartBoxRosserSplitRelativeBudget, dusartBoxSplitLowBound_self, min_self]
  rfl

/-- Splitting the low zeros sharpens the actual normalized average on the entire ray. -/
theorem abs_dusartPsiAverageError_div_le_split_frozen (m : ℕ) {s x x₀ R p a U H δ : ℝ}
    (hs : 0 < s) (hx₀ : 1 < x₀) (hx : x₀ ≤ x) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haU : a < U) (hUH : U ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxRosserSplitRelativeBudget m s x₀ R p a U H δ := by
  have hx1 : 1 < x := hx₀.trans_le hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx1
  let L := min (((1 + (m + 3 : ℕ) * s) * exp (-δ * Real.log x₀)) *
    xiLowReciprocalNormBound a H δ) (dusartBoxSplitLowBound m s x₀ a U H δ)
  let V := (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
    xiRosserClosedTailBound (Real.log x₀ / R) (m + 4 : ℕ) p H
  have hl : ‖∑ z ∈ xiLowHeightIndices H, iteratedBoxAverageComplex (s * x) (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x‖ / x ≤ L :=
    le_min (norm_dusartBox_low_div_le_frozen m hs hx₀ hx ha (haU.trans_le hUH) hδ hgap)
      (norm_dusartBox_low_div_le_split_frozen m hs hx₀ hx ha haU hUH hδ hgap)
  have hu : ‖dusartBoxXiHighSum m (s * x) x H‖ / x ≤ V :=
    norm_dusartBoxXiHighSum_div_le_frozen_closed m hs hx₀ hx hR hp hpq
      (by linarith) hpeak hreg
  have hz : ‖smoothedXiPairedSum (fun u => (dusartBoxWeight m (s * x) x u : ℂ))
      (dusartBoxSupport m (s * x) x) 0‖ / x ≤ L + V := by
    rw [smoothedXiPairedSum_box_eq_low_add_high m (mul_pos hs hxpos) hx1 H]
    exact (div_le_div_of_nonneg_right (norm_add_le _ _) hxpos.le).trans
      (by rw [add_div]; exact add_le_add hl hu)
  have hb := div_le_div_of_nonneg_right
    (abs_dusartPsiAverageError_le_zero_sum m (mul_pos hs hxpos) hx1) hxpos.le
  calc
    _ ≤ (‖smoothedXiPairedSum (fun u => (dusartBoxWeight m (s * x) x u : ℂ))
        (dusartBoxSupport m (s * x) x) 0‖ + 1 / (2 * (x ^ 2 - 1)) +
          Real.log (2 * π)) / x := hb
    _ = ‖smoothedXiPairedSum (fun u => (dusartBoxWeight m (s * x) x u : ℂ))
        (dusartBoxSupport m (s * x) x) 0‖ / x +
          (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x := by ring
    _ ≤ L + V + (1 / (2 * (x₀ ^ 2 - 1)) + Real.log (2 * π)) / x₀ :=
      add_le_add hz (dusartBox_relative_correction_le hx₀ hx)
    _ = _ := rfl

end

end PrimeFactorUnimodality
