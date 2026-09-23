import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxCoefficientStability

/-! # Finite numerical inputs for a midpoint coefficient

The existing primitive identity reduces one coefficient to a short binomial
sum of divided powers. This module exposes the precise sample error cost;
the stability theorem then extends the checked midpoint to its whole row.
High precision is required only for these point evaluations, not for an
interval expression that repeatedly contains the unknown zero ordinate.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Finset Function intervalIntegral

/-- The exact denominator is rational complex when the step and ordinate are rational. -/
def dusartBoxCoefficientDenom (m : ℕ) (s γ : ℝ) : ℂ :=
  (s : ℂ) ^ (m + 3) * cpowPrimitiveDenom ((1 / 2 : ℂ) + γ * I) (m + 3)

/-- The short signed binomial combination of supplied power samples. -/
def dusartBoxCoefficientNumerator (m : ℕ) (v : ℕ → ℂ) : ℂ :=
  ∑ j ∈ range (m + 4), ((-1 : ℤ) ^ (m + 3 - j) * (m + 3).choose j) • v j

private theorem criticalLine_add_nat_ne_zero (γ : ℝ) (j : ℕ) :
    (1 / 2 : ℂ) + γ * I + j ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  simp at hr
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

/-- Every denominator factor is nonzero, including for a zero center ordinate. -/
theorem dusartBoxCoefficientDenom_ne_zero (m : ℕ) {s : ℝ} (hs : 0 < s) (γ : ℝ) :
    dusartBoxCoefficientDenom m s γ ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (ofReal_ne_zero.mpr hs.ne'))
    (cpowPrimitiveDenom_ne_zero (criticalLine_add_nat_ne_zero γ) _)

/-- A coefficient is exactly its finite power-sample numerator, denominator and unit phase. -/
theorem dusartBoxOrdinateCoefficient_eq_samples (m : ℕ) {s : ℝ} (hs : 0 < s) (u γ : ℝ) :
    dusartBoxOrdinateCoefficient m s u γ =
      dusartBoxCoefficientNumerator m
        (fun j => ((1 + j • s : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + γ * I + (m + 3 : ℕ))) /
          dusartBoxCoefficientDenom m s γ * exp (I * ↑(u * γ)) := by
  unfold dusartBoxOrdinateCoefficient
  rw [iteratedBoxAverageComplex_cpow_div_eq_difference hs zero_lt_one
    (criticalLine_add_nat_ne_zero γ), fwdDiff_iter_eq_sum_shift]
  rfl

/-- Each sample error is charged with its exact binomial weight before denominator scaling. -/
theorem norm_dusartBoxOrdinateCoefficient_sub_samples_le (m : ℕ) {s : ℝ}
    (hs : 0 < s) (u γ : ℝ) (v : ℕ → ℂ) (e : ℕ → ℝ)
    (he : ∀ j ∈ range (m + 4),
      ‖((1 + j • s : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + γ * I + (m + 3 : ℕ)) - v j‖ ≤ e j) :
    ‖dusartBoxOrdinateCoefficient m s u γ -
      dusartBoxCoefficientNumerator m v / dusartBoxCoefficientDenom m s γ *
        exp (I * ↑(u * γ))‖ ≤
      (∑ j ∈ range (m + 4), ((m + 3).choose j : ℝ) * e j) /
        ‖dusartBoxCoefficientDenom m s γ‖ := by
  have hd := norm_fwdDiff_iter_sub_sum_le s 1 (m + 3)
    (fun t : ℝ => (t : ℂ) ^ ((1 / 2 : ℂ) + γ * I + (m + 3 : ℕ))) v e he
  rw [fwdDiff_iter_eq_sum_shift] at hd
  change ‖dusartBoxCoefficientNumerator m
    (fun j => ((1 + j • s : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + γ * I + (m + 3 : ℕ))) -
      dusartBoxCoefficientNumerator m v‖ ≤ _ at hd
  rw [dusartBoxOrdinateCoefficient_eq_samples m hs, ← sub_mul, ← sub_div, norm_mul, norm_div]
  have hp : ‖exp (I * ↑(u * γ))‖ = 1 := by simp [norm_exp, mul_re]
  rw [hp, mul_one]
  exact div_le_div_of_nonneg_right hd (norm_nonneg _)

/-- Power samples, a phase enclosure and final arithmetic rounding give a checked coefficient. -/
theorem norm_dusartBoxOrdinateCoefficient_sub_checked_samples_le (m : ℕ) {s : ℝ}
    (hs : 0 < s) (u γ : ℝ) (v : ℕ → ℂ) (e : ℕ → ℝ)
    (he : ∀ j ∈ range (m + 4),
      ‖((1 + j • s : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + γ * I + (m + 3 : ℕ)) - v j‖ ≤ e j)
    {p c : ℂ} {η r : ℝ} (hp : ‖exp (I * ↑(u * γ)) - p‖ ≤ η)
    (hc : ‖dusartBoxCoefficientNumerator m v / dusartBoxCoefficientDenom m s γ * p - c‖ ≤ r) :
    ‖dusartBoxOrdinateCoefficient m s u γ - c‖ ≤
      (∑ j ∈ range (m + 4), ((m + 3).choose j : ℝ) * e j) /
          ‖dusartBoxCoefficientDenom m s γ‖ +
        ‖dusartBoxCoefficientNumerator m v / dusartBoxCoefficientDenom m s γ‖ * η + r := by
  let q := dusartBoxCoefficientNumerator m v / dusartBoxCoefficientDenom m s γ
  have hphase : ‖q * exp (I * ↑(u * γ)) - q * p‖ ≤ ‖q‖ * η := by
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left hp (norm_nonneg q)
  have happrox := (norm_sub_le_norm_sub_add_norm_sub
    (dusartBoxOrdinateCoefficient m s u γ) (q * exp (I * ↑(u * γ))) (q * p)).trans
      (add_le_add (norm_dusartBoxOrdinateCoefficient_sub_samples_le m hs u γ v e he) hphase)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (q * p) c).trans (add_le_add happrox hc)

end

end PrimeFactorUnimodality
