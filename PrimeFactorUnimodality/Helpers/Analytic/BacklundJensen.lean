import Mathlib.Analysis.Complex.JensenFormula
import PrimeFactorUnimodality.Helpers.Analytic.BacklundAuxiliary
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Powers.Recurrence

/-! # Jensen bounds for the actual Backlund auxiliary function

Compact recurrence chooses arbitrarily large powers with a quantitatively
nonzero centre value. Mathlib's Jensen inequality then bounds the complete
auxiliary divisor mass on a smaller disk. The logarithmic loss from this
choice is exactly `log 2`, independent of the power. The required uniform
surrogate norm bound and the argument-variation comparison are not assumed
proved here; neither is a numerical zero-count estimate.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter Metric Real
open scoped Topology

/-- Complete zero multiplicity of the auxiliary function in a closed disk. -/
def backlundAuxiliaryZeroMass (T : ℝ) (n : ℕ) (σ r : ℝ) : ℝ :=
  ((∑ᶠ z : ℂ, MeromorphicOn.divisor (backlundAuxiliary T n) (closedBall (σ : ℂ) r) z : ℤ) : ℝ)

/-- The zero mass is nonnegative because the auxiliary function is entire. -/
theorem backlundAuxiliaryZeroMass_nonneg (T : ℝ) (n : ℕ) (σ r : ℝ) :
    0 ≤ backlundAuxiliaryZeroMass T n σ r := by
  have ha : AnalyticOnNhd ℂ (backlundAuxiliary T n) (closedBall (σ : ℂ) r) :=
    fun z _ => (differentiable_backlundAuxiliary T n).analyticAt z
  unfold backlundAuxiliaryZeroMass
  exact_mod_cast finsum_nonneg (fun z => MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha z)

/-- Arbitrarily large powers have a centre value at least half the corresponding norm power. -/
theorem frequently_backlundAuxiliary_centre_lower {σ : ℝ} (hσ : 1 < σ) (T : ℝ) :
    ∃ᶠ n : ℕ in atTop,
      ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖ ^ n / 2 ≤
        ‖backlundAuxiliary T n σ‖ := by
  have hne := backlund_surrogate_ne_zero_of_one_lt_re
    (show 1 < ((σ : ℂ) + T * I).re by simpa using hσ)
  apply (Complex.frequently_half_norm_pow_le_re_pow hne).mono
  intro n hn
  rw [backlundAuxiliary_ofReal, norm_real, Real.norm_eq_abs]
  exact hn.trans (le_abs_self _)

/-- Jensen's numerator has only the fixed `log 2` cost at a good power. -/
theorem backlundAuxiliaryZeroMass_le {σ T r R M : ℝ} {n : ℕ}
    (hσ : 1 < σ) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hc : ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖ ^ n / 2 ≤
      ‖backlundAuxiliary T n σ‖)
    (hp : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    backlundAuxiliaryZeroMass T n σ r ≤
      ((n : ℝ) * Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) + Real.log 2) /
        Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hMp : 0 < M := by linarith
  have hA : 0 < ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖ :=
    norm_pos_iff.mpr (backlund_surrogate_ne_zero_of_one_lt_re (by simpa using hσ))
  have hC : 0 < ‖backlundAuxiliary T n σ‖ :=
    (div_pos (pow_pos hA n) (by norm_num)).trans_le hc
  have ha : AnalyticOnNhd ℂ (backlundAuxiliary T n) (closedBall (σ : ℂ) |R|) :=
    fun z _ => (differentiable_backlundAuxiliary T n).analyticAt z
  have hj := ha.sum_divisor_le
    (c := (σ : ℂ)) (R := R) (r := r) (M := M ^ n) (by simpa only [abs_of_pos hr] using hr)
    (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR)
    (one_le_pow₀ hM) (norm_pos_iff.mp hC) (by
      intro z hz
      rw [abs_of_pos hR] at hz
      exact norm_backlundAuxiliary_le_pow (hp z hz) (hm z hz))
  have hlog : Real.log (M ^ n / ‖backlundAuxiliary T n σ‖) ≤
      (n : ℝ) * Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) + Real.log 2 := by
    calc
      _ ≤ Real.log (M ^ n / (‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖ ^ n / 2)) :=
        Real.log_le_log (div_pos (pow_pos hMp n) hC)
          (div_le_div_of_nonneg_left (pow_nonneg hMp.le n)
            (div_pos (pow_pos hA n) (by norm_num)) hc)
      _ = _ := by
        rw [Real.log_div (pow_pos hMp n).ne' (div_pos (pow_pos hA n) (by norm_num)).ne',
          Real.log_div (pow_pos hA n).ne' (by norm_num), Real.log_pow, Real.log_pow,
          Real.log_div hMp.ne' hA.ne']
        ring
  rw [abs_of_pos hr] at hj
  apply (show backlundAuxiliaryZeroMass T n σ r ≤
      Real.log (M ^ n / ‖backlundAuxiliary T n σ‖) / Real.log (R / r) from by
        exact hj).trans
  exact div_le_div_of_nonneg_right hlog (Real.log_nonneg ((one_le_div hr).mpr hrR.le))

/-- The Jensen bound is available at arbitrarily large powers of the source function. -/
theorem frequently_backlundAuxiliaryZeroMass_le {σ T r R M : ℝ}
    (hσ : 1 < σ) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hp : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    ∃ᶠ n : ℕ in atTop, backlundAuxiliaryZeroMass T n σ r ≤
      ((n : ℝ) * Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) + Real.log 2) /
        Real.log (R / r) :=
  (frequently_backlundAuxiliary_centre_lower hσ T).mono fun _ hc =>
    backlundAuxiliaryZeroMass_le hσ hr hrR hM hc hp hm

end

end PrimeFactorUnimodality
