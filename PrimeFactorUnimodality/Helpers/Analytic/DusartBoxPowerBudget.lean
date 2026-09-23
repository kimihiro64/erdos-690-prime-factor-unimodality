import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxLowSplit
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPowerTail
import PrimeFactorUnimodality.Helpers.Analytic.DusartPsiRelativeAverages

/-! # A uniform psi endpoint estimate from finite low-zero information

Combine the refined finite low block with the unconditional power
tail. Only the low-height real-part gap remains a zero-location
hypothesis. Two endpoint averages control the whole ray, including
prime-power jumps. Their scalar values are not assumed proved.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real intervalIntegral

/-- The explicit normalized average budget using the power tail. -/
def dusartBoxPowerRelativeBudget (m : ℕ) (s x a U H δ : ℝ) : ℝ :=
  min (((1 + (m + 3 : ℕ) * s) * exp (-δ * Real.log x)) * xiLowReciprocalNormBound a H δ)
    (dusartBoxSplitLowBound m s x a U H δ) +
    (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
      xiRosserPowerTailBound (m + 4 : ℕ) H +
    (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x

/-- Two starting-point values and the exact smoothing loss. -/
def dusartBoxPowerPsiBound (m : ℕ) (s x₀ a U H δ : ℝ) : ℝ :=
  let t := 1 - (m + 3 : ℕ) * s
  max (t * dusartBoxPowerRelativeBudget m (s / t) (x₀ * t) a U H δ)
    (dusartBoxPowerRelativeBudget m s x₀ a U H δ) + (m + 3 : ℕ) * s / 2

/-- Low-height information alone controls every later average. -/
theorem abs_dusartPsiAverageError_div_le_power_frozen (m : ℕ) {s x x₀ a U H δ : ℝ}
    (hs : 0 < s) (hx₀ : 1 < x₀) (hx : x₀ ≤ x)
    (ha : 10 ≤ a) (haU : a < U) (hUH : U ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxPowerRelativeBudget m s x₀ a U H δ := by
  have hx1 : 1 < x := hx₀.trans_le hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx1
  let L := min (((1 + (m + 3 : ℕ) * s) * exp (-δ * Real.log x₀)) *
    xiLowReciprocalNormBound a H δ) (dusartBoxSplitLowBound m s x₀ a U H δ)
  let V := (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
    xiRosserPowerTailBound (m + 4 : ℕ) H
  have hl : ‖∑ z ∈ xiLowHeightIndices H, iteratedBoxAverageComplex (s * x) (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x‖ / x ≤ L :=
    le_min (norm_dusartBox_low_div_le_frozen m hs hx₀ hx ha (haU.trans_le hUH) hδ hgap)
      (norm_dusartBox_low_div_le_split_frozen m hs hx₀ hx ha haU hUH hδ hgap)
  have hu : ‖dusartBoxXiHighSum m (s * x) x H‖ / x ≤ V :=
    norm_dusartBoxXiHighSum_div_le_power m hs hx1 (by linarith)
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

/-- The actual relative psi error is bounded on the entire ray. -/
theorem abs_psi_sub_div_le_power_frozen (m : ℕ) {s x x₀ a U H δ : ℝ}
    (hs : 0 < s) (hx₀ : 0 < x₀) (hx : x₀ ≤ x)
    (hl₀ : 1 < x₀ * (1 - (m + 3 : ℕ) * s))
    (ha : 10 ≤ a) (haU : a < U) (hUH : U ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ) :
    |ψ x - x| / x ≤ dusartBoxPowerPsiBound m s x₀ a U H δ := by
  let t := 1 - (m + 3 : ℕ) * s
  have ht : 0 < t := (mul_pos_iff_of_pos_left hx₀).mp (lt_trans zero_lt_one hl₀)
  have ht1 : t ≤ 1 := sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hs.le)
  have hlx₀ : x₀ * t ≤ x₀ := by nlinarith
  have hx₀1 : 1 < x₀ := hl₀.trans_le hlx₀
  have hxpos : 0 < x := hx₀.trans_le hx
  have hleft : x₀ * t ≤ x * t := mul_le_mul_of_nonneg_right hx ht.le
  have hleftpos : 0 < x * t := mul_pos hxpos ht
  have hl := abs_dusartPsiAverageError_div_le_power_frozen m (div_pos hs ht) hl₀ hleft
    ha haU hUH hδ hgap
  have hstep : (s / t) * (x * t) = s * x := by field_simp
  rw [hstep] at hl
  exact dusart_abs_psi_div_le_of_relative_averages (m + 3) hs hxpos hleftpos hl
    (abs_dusartPsiAverageError_div_le_power_frozen m hs hx₀1 hx
      ha haU hUH hδ hgap)

end

end PrimeFactorUnimodality
