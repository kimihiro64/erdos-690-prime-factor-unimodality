import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserFrozenAverage

/-! # Higher-order decay inside the verified low-zero block

Split the low block at an adjustable inner height. Keep reciprocal-norm
control below it and retain both the real-part gap and full height power
above it. Equal cutoffs have exactly zero band cost. All divisor labels
and both ordinate signs are included by the existing partition.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real intervalIntegral

/-- Higher-order smoothing preserves the strong real-part gap on a finite band. -/
theorem norm_dusartBox_band_le_gap_tail (m : ℕ) {h x U H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hU : 1 < U) (hδ : 0 ≤ δ)
    (hgap : ∀ z ∈ xiHeightBandIndices U H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ) :
    ‖∑ z ∈ xiHeightBandIndices U H, iteratedBoxAverageComplex h (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x‖ ≤
      ((2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        exp (-δ * Real.log x)) * xiRosserAbsoluteTail 0 (m + 4 : ℕ) U := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  let C := (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
    exp (-δ * Real.log x)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp (z : RiemannXiDivisorZeroIndex) (hz : z ∈ xiHeightBandIndices U H) :
      ‖iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x‖ ≤
        C * logDampedPower 0 (m + 4 : ℕ) |(riemannXiDivisorZeroValue z).im| := by
    have hγ : 0 < |(riemannXiDivisorZeroValue z).im| :=
      (lt_trans zero_lt_one hU).trans_le ((mem_xiHeightBandIndices U H z).mp hz).1
    have hb := norm_dusartBox_paired_atom_le_height_gap m hh hx hδ (abs_pos.mp hγ)
      (riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero z)).1 (hgap z hz)
    rw [finiteLaplace_dusartBoxWeight_add_inv m hh hx (riemannXiDivisorZeroValue_ne_zero z)] at hb
    refine hb.trans_eq ?_
    rw [logDampedPower_eq_rpow_mul hγ, Real.rpow_neg hγ.le, Real.rpow_natCast]
    simp only [neg_zero, zero_div, Real.exp_zero, mul_one]
    dsimp [C]
    ring
  calc
    _ ≤ ∑ z ∈ xiHeightBandIndices U H,
        C * logDampedPower 0 (m + 4 : ℕ) |(riemannXiDivisorZeroValue z).im| :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hp)
    _ = C * ∑ z ∈ xiHeightBandIndices U H,
        logDampedPower 0 (m + 4 : ℕ) |(riemannXiDivisorZeroValue z).im| := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_xi_logDampedPower_le_absoluteTail le_rfl
        (by norm_cast; omega : (2 : ℝ) ≤ (m + 4 : ℕ)) hU _
        (fun z hz => ((mem_xiHeightBandIndices U H z).mp hz).1)) hC

/-- A finite band's power-tail cost vanishes when its cutoffs coincide. -/
def xiRosserPowerBandBound (q U H : ℝ) : ℝ :=
  if U < H then xiRosserPowerTailBound q U else 0

@[simp] theorem xiRosserPowerBandBound_self (q U : ℝ) :
    xiRosserPowerBandBound q U U = 0 := by simp [xiRosserPowerBandBound]

/-- The elementary band cost is nonnegative. -/
theorem xiRosserPowerBandBound_nonneg {q U H : ℝ} (hq : 2 ≤ q) (hU : 10 < U) :
    0 ≤ xiRosserPowerBandBound q U H := by
  have ht : 0 ≤ xiRosserPowerTailBound q U :=
    (tsum_nonneg (fun _ => (logDampedPower_pos _ _ _).le)).trans
      (xiRosserAbsoluteTail_zero_le_power hq hU)
  unfold xiRosserPowerBandBound
  split_ifs <;> positivity

/-- Full-power decay gives an elementary bound on the actual band, including zero width. -/
theorem norm_dusartBox_band_le_gap_power (m : ℕ) {h x U H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hU : 10 < U) (hUH : U ≤ H) (hδ : 0 ≤ δ)
    (hgap : ∀ z ∈ xiHeightBandIndices U H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ) :
    ‖∑ z ∈ xiHeightBandIndices U H, iteratedBoxAverageComplex h (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x‖ ≤
      ((2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        exp (-δ * Real.log x)) * xiRosserPowerBandBound (m + 4 : ℕ) U H := by
  by_cases hlt : U < H
  · have hxpos : 0 < x := lt_trans zero_lt_one hx
    rw [xiRosserPowerBandBound, ite_eq_left hlt]
    exact (norm_dusartBox_band_le_gap_tail m hh hx (by linarith) hδ hgap).trans
      (mul_le_mul_of_nonneg_left
        (xiRosserAbsoluteTail_zero_le_power (by norm_cast; omega) hU) (by positivity))
  · have he : U = H := le_antisymm hUH (le_of_not_gt hlt)
    subst H
    simp

/-- The two-term low block with an adjustable inner cutoff and a fixed relative step. -/
def dusartBoxSplitLowBound (m : ℕ) (s x a U H δ : ℝ) : ℝ :=
  exp (-δ * Real.log x) *
    ((1 + (m + 3 : ℕ) * s) * xiLowReciprocalNormBound a U δ +
      (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
        xiRosserPowerBandBound (m + 4 : ℕ) U H)

/-- At equal cutoffs, the split estimate is exactly the original low-block estimate. -/
theorem dusartBoxSplitLowBound_self (m : ℕ) (s x a H δ : ℝ) :
    dusartBoxSplitLowBound m s x a H H δ =
      ((1 + (m + 3 : ℕ) * s) * exp (-δ * Real.log x)) *
        xiLowReciprocalNormBound a H δ := by
  simp only [dusartBoxSplitLowBound, xiRosserPowerBandBound_self, mul_zero, add_zero]
  ring

/-- The actual entire low block is bounded uniformly using both decay estimates. -/
theorem norm_dusartBox_low_div_le_split_frozen (m : ℕ) {s x x₀ a U H δ : ℝ}
    (hs : 0 < s) (hx₀ : 1 < x₀) (hx : x₀ ≤ x)
    (ha : 10 ≤ a) (haU : a < U) (hUH : U ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ) :
    ‖∑ z ∈ xiLowHeightIndices H, iteratedBoxAverageComplex (s * x) (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x‖ / x ≤
      dusartBoxSplitLowBound m s x₀ a U H δ := by
  classical
  let : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _
  have hx1 : 1 < x := hx₀.trans_le hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx1
  have hgapU : ∀ z ∈ xiLowHeightIndices U, (riemannXiDivisorZeroValue z).re ≤ 1 - δ := by
    intro z hz
    exact hgap z ((mem_xiLowHeightIndices H z).mpr
      (((mem_xiLowHeightIndices U z).mp hz).trans_le hUH))
  have hgapBand : ∀ z ∈ xiHeightBandIndices U H,
      (riemannXiDivisorZeroValue z).re ≤ 1 - δ := by
    intro z hz
    exact hgap z ((mem_xiLowHeightIndices H z).mpr ((mem_xiHeightBandIndices U H z).mp hz).2)
  let C := 2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)
  let B := xiRosserPowerBandBound (m + 4 : ℕ) U H
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : 0 ≤ B := xiRosserPowerBandBound_nonneg (by norm_cast; omega) (by linarith)
  have hd : exp (-δ * Real.log x) ≤ exp (-δ * Real.log x₀) := by
    apply Real.exp_le_exp.mpr
    have hlog := mul_le_mul_of_nonneg_left
      (Real.log_le_log (lt_trans zero_lt_one hx₀) hx) hδ.le
    linarith only [hlog]
  have hc : 2 ^ (m + 3) * (x + (m + 3 : ℕ) * (s * x)) ^ (m + 4) /
      (s * x) ^ (m + 3) = x * C := by
    rw [show x + (m + 3 : ℕ) * (s * x) = x * (1 + (m + 3 : ℕ) * s) by ring,
      mul_pow, mul_pow, show m + 4 = (m + 3) + 1 by omega, pow_succ x]
    dsimp [C]
    field_simp
  let F := fun z => iteratedBoxAverageComplex (s * x) (m + 3)
    (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x
  have hb : ‖∑ z ∈ xiHeightBandIndices U H, F z‖ / x ≤
      exp (-δ * Real.log x₀) * (C * B) := by
    have hb := norm_dusartBox_band_le_gap_power m (mul_pos hs hxpos) hx1
      (by linarith) hUH hδ.le hgapBand
    rw [hc] at hb
    apply (div_le_iff₀ hxpos).mpr
    calc
      _ ≤ (x * C * exp (-δ * Real.log x)) * B := hb
      _ ≤ (x * C * exp (-δ * Real.log x₀)) * B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (mul_nonneg hxpos.le hC)) hB
      _ = _ := by ring
  have hsplit : (∑ z ∈ xiLowHeightIndices H, F z) =
      (∑ z ∈ xiLowHeightIndices U, F z) + (∑ z ∈ xiHeightBandIndices U H, F z) := by
    have he := Finset.sum_union (f := F) (disjoint_xiLowHeightIndices_band U H)
    rw [xiLowHeightIndices_union_band hUH] at he
    exact he
  change ‖∑ z ∈ xiLowHeightIndices H, F z‖ / x ≤ _
  rw [hsplit]
  calc
    _ ≤ ‖∑ z ∈ xiLowHeightIndices U, F z‖ / x +
        ‖∑ z ∈ xiHeightBandIndices U H, F z‖ / x := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (norm_add_le _ _) hxpos.le
    _ ≤ ((1 + (m + 3 : ℕ) * s) * exp (-δ * Real.log x₀)) *
        xiLowReciprocalNormBound a U δ + exp (-δ * Real.log x₀) * (C * B) :=
      add_le_add (norm_dusartBox_low_div_le_frozen m hs hx₀ hx ha haU hδ hgapU) hb
    _ = _ := by dsimp [dusartBoxSplitLowBound, C, B]; ring

end

end PrimeFactorUnimodality
