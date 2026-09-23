import PrimeFactorUnimodality.Helpers.Analytic.DusartReducedPsiEndpoint

/-! # The published upper theta margin from explicit endpoint arithmetic

The legacy order-three scalar budgets remain available. The actual psi
theorem now applies the order-five estimate in `DusartReducedPsiEndpoint`,
restricting its original billion-height zero premise to height 25000000.
The normalized error remains below 1/36260 above 1441000000000. Finite
zero verification remains an explicit hypothesis; it is not proved here.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Both adjacent relative steps fit inside one rational width bound. -/
theorem dusartEndpoint_width_le {s : ℝ} (hs : s ≤ (1 / 449997 : ℝ)) :
    1 + 3 * s ≤ (1000007 / 1000000 : ℝ) := by linarith

/-- A single rational coefficient controls both adjacent high tails. -/
theorem dusartEndpoint_high_coefficient_le {s : ℝ} (hs₀ : (1 / 450000 : ℝ) ≤ s)
    (hs₁ : s ≤ (1 / 449997 : ℝ)) :
    8 * (1 + 3 * s) ^ 4 / s ^ 3 ≤ (7291 * 10 ^ 14 : ℝ) := by
  have hspos : 0 < s := by linarith
  have hw := dusartEndpoint_width_le hs₁
  have hn := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 3 * s) hw 4
  have hd := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 450000) hs₀ 3
  calc
    _ ≤ 8 * (1000007 / 1000000 : ℝ) ^ 4 / s ^ 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) (by positivity)
    _ ≤ 8 * (1000007 / 1000000 : ℝ) ^ 4 / (1 / 450000 : ℝ) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
    _ ≤ _ := by norm_num

/-- The rational bound on either starting-point average. -/
def dusartEndpointAverageCap : ℝ :=
  ((1000007 / 1000000) * (561 / 20) + (7291 * 10 ^ 14) * (131 / 10 ^ 20)) / 1200000 +
    (7291 * 10 ^ 14) * (205 / 10 ^ 29) + 4 / 1440000000000

/-- The complete average budget is below the evaluated rational cap. -/
theorem dusartBoxPowerRelativeBudget_endpoint_le {s x : ℝ} (hs₀ : (1 / 450000 : ℝ) ≤ s)
    (hs₁ : s ≤ (1 / 449997 : ℝ)) (hx : (1440000000000 : ℝ) ≤ x) :
    dusartBoxPowerRelativeBudget 0 s x 10 1000000 1000000000 (1 / 2) ≤
      dusartEndpointAverageCap := by
  have hspos : 0 < s := by linarith
  have he := dusartEndpoint_half_log_decay_le hx
  have hc := dusartEndpoint_high_coefficient_le hs₀ hs₁
  have hc0 : 0 ≤ 8 * (1 + 3 * s) ^ 4 / s ^ 3 := by positivity
  have hlow : (1 + 3 * s) * xiLowReciprocalNormBound 10 1000000 (1 / 2) ≤
      (1000007 / 1000000 : ℝ) * (561 / 20) :=
    (mul_le_mul_of_nonneg_left xiLowReciprocalNormBound_million_half_le (by positivity)).trans
      (mul_le_mul_of_nonneg_right (dusartEndpoint_width_le hs₁) (by norm_num))
  have hband : (8 * (1 + 3 * s) ^ 4 / s ^ 3) * xiRosserPowerTailBound 4 1000000 ≤
      (7291 * 10 ^ 14 : ℝ) * (131 / 10 ^ 20) :=
    (mul_le_mul_of_nonneg_left xiRosserPowerTailBound_four_million_le hc0).trans
      (mul_le_mul_of_nonneg_right hc (by norm_num))
  have hhigh : (8 * (1 + 3 * s) ^ 4 / s ^ 3) * xiRosserPowerTailBound 4 1000000000 ≤
      (7291 * 10 ^ 14 : ℝ) * (205 / 10 ^ 29) :=
    (mul_le_mul_of_nonneg_left xiRosserPowerTailBound_four_billion_le hc0).trans
      (mul_le_mul_of_nonneg_right hc (by norm_num))
  have hsplit : dusartBoxSplitLowBound 0 s x 10 1000000 1000000000 (1 / 2) ≤
      ((1000007 / 1000000 : ℝ) * (561 / 20) +
        (7291 * 10 ^ 14) * (131 / 10 ^ 20)) / 1200000 := by
    unfold dusartBoxSplitLowBound xiRosserPowerBandBound
    norm_num only [Nat.cast_ofNat, zero_add, show (1000000 : ℝ) < 1000000000 by norm_num,
      ite_true, show (2 : ℝ) ^ (3 : ℕ) = 8 by norm_num]
    exact ((mul_le_mul_of_nonneg_left (add_le_add hlow hband) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right he (by norm_num))).trans_eq (by ring)
  unfold dusartBoxPowerRelativeBudget dusartEndpointAverageCap
  simp only [Nat.cast_ofNat, zero_add, show (2 : ℝ) ^ (3 : ℕ) = 8 by norm_num]
  exact add_le_add (add_le_add ((min_le_right _ _).trans hsplit) hhigh)
    (dusartEndpoint_correction_le hx)

/-- The two-average budget satisfies the published relative upper margin. -/
theorem dusartBoxPowerPsiBound_endpoint_lt {x₀ : ℝ} (hx₀ : (1441000000000 : ℝ) ≤ x₀) :
    dusartBoxPowerPsiBound 0 (1 / 450000) x₀ 10 1000000 1000000000 (1 / 2) <
      (1 / 36260 : ℝ) := by
  have hleft : (1440000000000 : ℝ) ≤ x₀ * (1 - 3 * (1 / 450000)) := by linarith
  have hl := dusartBoxPowerRelativeBudget_endpoint_le (s := (1 / 450000) / (1 - 3 * (1 / 450000)))
    (by norm_num) (by norm_num) hleft
  have hr := dusartBoxPowerRelativeBudget_endpoint_le (s := 1 / 450000) (by norm_num) (by norm_num)
    (by linarith : (1440000000000 : ℝ) ≤ x₀)
  have hb : (1 - 3 * (1 / 450000) : ℝ) *
      dusartBoxPowerRelativeBudget 0 ((1 / 450000) / (1 - 3 * (1 / 450000)))
        (x₀ * (1 - 3 * (1 / 450000))) 10 1000000 1000000000 (1 / 2) ≤ dusartEndpointAverageCap :=
    (mul_le_mul_of_nonneg_left hl (by norm_num)).trans (by norm_num [dusartEndpointAverageCap])
  unfold dusartBoxPowerPsiBound
  simp only [Nat.cast_ofNat, zero_add]
  apply lt_of_le_of_lt (add_le_add (max_le hb hr) (le_refl (3 * (1 / 450000 : ℝ) / 2)))
  norm_num [dusartEndpointAverageCap]

/-- Only the finite low-zero gap remains in the actual uniform psi estimate. -/
theorem abs_psi_sub_div_lt_of_billion_low_gap {x : ℝ} (hx : (1441000000000 : ℝ) ≤ x)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.psi x - x| / x < (1 / 36260 : ℝ) := by
  apply abs_psi_sub_div_lt_of_reduced_low_gap hx
  intro z hz
  apply hgap z
  rw [mem_xiLowHeightIndices] at hz ⊢
  linarith

/-- The exact published theta upper margin follows on the entire ray. -/
theorem theta_lt_dusart_upper_of_billion_low_gap {x : ℝ} (hx : (1441000000000 : ℝ) ≤ x)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    Chebyshev.theta x < x * (1 + 1 / 36260) := by
  have hp := (div_lt_iff₀ (by linarith : 0 < x)).mp (abs_psi_sub_div_lt_of_billion_low_gap hx hgap)
  have ha := le_abs_self (Chebyshev.psi x - x)
  have ht := Chebyshev.theta_le_psi x
  linarith

end

end PrimeFactorUnimodality
