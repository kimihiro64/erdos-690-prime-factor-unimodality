import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPowerBudget
import PrimeFactorUnimodality.Helpers.Analytic.DusartEndpointElementary
import PrimeFactorUnimodality.Helpers.Analytic.XiReducedCutoffBounds

/-! # A psi endpoint using zeros only below twenty-five million

Order five, relative step 1/600000, and inner height 1250000 give the
published relative margin on the full ray above 1441000000000. The
positive-prefix half-mass bound permits outer height 25000000. All scalar
bounds are proved; actual low-zero verification remains an explicit input.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Both adjacent relative steps fit inside one rational width bound. -/
theorem dusartReducedEndpoint_width_le {s : ℝ} (hs : s ≤ (1 / 599995 : ℝ)) :
    1 + 5 * s ≤ (1000009 / 1000000 : ℝ) := by linarith

/-- A single rational coefficient controls both adjacent high tails. -/
theorem dusartReducedEndpoint_high_coefficient_le {s : ℝ} (hs₀ : (1 / 600000 : ℝ) ≤ s)
    (hs₁ : s ≤ (1 / 599995 : ℝ)) :
    32 * (1 + 5 * s) ^ 6 / s ^ 5 ≤ (249 * 10 ^ 28 : ℝ) := by
  have hspos : 0 < s := by linarith
  have hw := dusartReducedEndpoint_width_le hs₁
  have hn := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 5 * s) hw 6
  have hd := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 600000) hs₀ 5
  calc
    _ ≤ 32 * (1000009 / 1000000 : ℝ) ^ 6 / s ^ 5 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) (by positivity)
    _ ≤ 32 * (1000009 / 1000000 : ℝ) ^ 6 / (1 / 600000 : ℝ) ^ 5 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
    _ ≤ _ := by norm_num

/-- The rational bound on either starting-point average. -/
def dusartReducedEndpointAverageCap : ℝ :=
  ((1000009 / 1000000) * (13393 / 500) + (249 * 10 ^ 28) * (26 / 10 ^ 32)) / 1200000 +
    (249 * 10 ^ 28) * (102 / 10 ^ 39) + 4 / 1440000000000

/-- The complete average budget is below the evaluated rational cap. -/
theorem dusartBoxPowerRelativeBudget_reduced_endpoint_le {s x : ℝ} (hs₀ : (1 / 600000 : ℝ) ≤ s)
    (hs₁ : s ≤ (1 / 599995 : ℝ)) (hx : (1440000000000 : ℝ) ≤ x) :
    dusartBoxPowerRelativeBudget 2 s x 25 1250000 25000000 (1 / 2) ≤
      dusartReducedEndpointAverageCap := by
  have hspos : 0 < s := by linarith
  have he := dusartEndpoint_half_log_decay_le hx
  have hc := dusartReducedEndpoint_high_coefficient_le hs₀ hs₁
  have hc0 : 0 ≤ 32 * (1 + 5 * s) ^ 6 / s ^ 5 := by positivity
  have hlow : (1 + 5 * s) * xiLowReciprocalNormBound 25 1250000 (1 / 2) ≤
      (1000009 / 1000000 : ℝ) * (13393 / 500) :=
    (mul_le_mul_of_nonneg_left xiLowReciprocalNormBound_reduced_le (by positivity)).trans
      (mul_le_mul_of_nonneg_right (dusartReducedEndpoint_width_le hs₁) (by norm_num))
  have hband : (32 * (1 + 5 * s) ^ 6 / s ^ 5) * xiRosserPowerTailBound 6 1250000 ≤
      (249 * 10 ^ 28 : ℝ) * (26 / 10 ^ 32) :=
    (mul_le_mul_of_nonneg_left xiRosserPowerTailBound_six_inner_reduced_le hc0).trans
      (mul_le_mul_of_nonneg_right hc (by norm_num))
  have hhigh : (32 * (1 + 5 * s) ^ 6 / s ^ 5) * xiRosserPowerTailBound 6 25000000 ≤
      (249 * 10 ^ 28 : ℝ) * (102 / 10 ^ 39) :=
    (mul_le_mul_of_nonneg_left xiRosserPowerTailBound_six_outer_reduced_le hc0).trans
      (mul_le_mul_of_nonneg_right hc (by norm_num))
  have hsplit : dusartBoxSplitLowBound 2 s x 25 1250000 25000000 (1 / 2) ≤
      ((1000009 / 1000000 : ℝ) * (13393 / 500) +
        (249 * 10 ^ 28) * (26 / 10 ^ 32)) / 1200000 := by
    unfold dusartBoxSplitLowBound xiRosserPowerBandBound
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd, show (1250000 : ℝ) < 25000000 by norm_num,
      ite_true, show (2 : ℝ) ^ (5 : ℕ) = 32 by norm_num]
    exact ((mul_le_mul_of_nonneg_left (add_le_add hlow hband) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right he (by norm_num))).trans_eq (by ring)
  unfold dusartBoxPowerRelativeBudget dusartReducedEndpointAverageCap
  simp only [Nat.cast_ofNat, Nat.reduceAdd, show (2 : ℝ) ^ (5 : ℕ) = 32 by norm_num]
  exact add_le_add (add_le_add ((min_le_right _ _).trans hsplit) hhigh)
    (dusartEndpoint_correction_le hx)

/-- The two-average budget satisfies the published relative upper margin. -/
theorem dusartBoxPowerPsiBound_reduced_endpoint_lt {x₀ : ℝ} (hx₀ : (1441000000000 : ℝ) ≤ x₀) :
    dusartBoxPowerPsiBound 2 (1 / 600000) x₀ 25 1250000 25000000 (1 / 2) <
      (1 / 36260 : ℝ) := by
  have hleft : (1440000000000 : ℝ) ≤ x₀ * (1 - 5 * (1 / 600000)) := by linarith
  have hl := dusartBoxPowerRelativeBudget_reduced_endpoint_le (s := (1 / 600000) / (1 - 5 * (1 / 600000)))
    (by norm_num) (by norm_num) hleft
  have hr := dusartBoxPowerRelativeBudget_reduced_endpoint_le (s := 1 / 600000) (by norm_num) (by norm_num)
    (by linarith : (1440000000000 : ℝ) ≤ x₀)
  have hb : (1 - 5 * (1 / 600000) : ℝ) *
      dusartBoxPowerRelativeBudget 2 ((1 / 600000) / (1 - 5 * (1 / 600000)))
        (x₀ * (1 - 5 * (1 / 600000))) 25 1250000 25000000 (1 / 2) ≤ dusartReducedEndpointAverageCap :=
    (mul_le_mul_of_nonneg_left hl (by norm_num)).trans (by norm_num [dusartReducedEndpointAverageCap])
  unfold dusartBoxPowerPsiBound
  simp only [Nat.cast_ofNat, Nat.reduceAdd]
  apply lt_of_le_of_lt (add_le_add (max_le hb hr) (le_refl (5 * (1 / 600000 : ℝ) / 2)))
  norm_num [dusartReducedEndpointAverageCap]

/-- Only the finite low-zero gap remains in the actual uniform psi estimate. -/
theorem abs_psi_sub_div_lt_of_reduced_low_gap {x : ℝ} (hx : (1441000000000 : ℝ) ≤ x)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.psi x - x| / x < (1 / 36260 : ℝ) := by
  have hb := abs_psi_sub_div_le_power_frozen (x₀ := (1441000000000 : ℝ))
    (s := 1 / 600000) (a := 25) (U := 1250000) (H := 25000000) (δ := 1 / 2)
    2 (by norm_num) (by norm_num) hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] using hgap)
  exact hb.trans_lt (dusartBoxPowerPsiBound_reduced_endpoint_lt le_rfl)

/-- The exact published theta upper margin follows on the entire ray. -/
theorem theta_lt_dusart_upper_of_reduced_low_gap {x : ℝ} (hx : (1441000000000 : ℝ) ≤ x)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    Chebyshev.theta x < x * (1 + 1 / 36260) := by
  have hp := (div_lt_iff₀ (by linarith : 0 < x)).mp (abs_psi_sub_div_lt_of_reduced_low_gap hx hgap)
  have ha := le_abs_self (Chebyshev.psi x - x)
  have ht := Chebyshev.theta_le_psi x
  linarith

end

end PrimeFactorUnimodality
