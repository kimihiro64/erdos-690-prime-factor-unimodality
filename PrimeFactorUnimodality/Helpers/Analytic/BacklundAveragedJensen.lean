import PrimeFactorUnimodality.Helpers.Analytic.BacklundArgumentIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.JensenAverage

/-! # The horizontal argument bound using the actual circle average

Keep Jensen's logarithmic mean rather than replacing it by the largest
circle value. The existing crossing-count and infinite-power limit apply
unchanged, including the fixed `log 2` centre loss.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter Metric Real Set
open scoped Topology

/-- The auxiliary zero mass is bounded by any proved linear logarithmic mean. -/
theorem backlundAuxiliaryZeroMass_le_average {σ T r R B : ℝ} {n : ℕ}
    (hσ : 1 < σ) (hr : 0 < r) (hrR : r < R)
    (hc : ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖ ^ n / 2 ≤
      ‖backlundAuxiliary T n σ‖)
    (hb : circleAverage (fun z => Real.log ‖backlundAuxiliary T n z‖) σ R ≤ (n : ℝ) * B) :
    backlundAuxiliaryZeroMass T n σ r ≤
      ((n : ℝ) * (B - Real.log ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) +
        Real.log 2) / Real.log (R / r) := by
  have hA : 0 < ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖ :=
    norm_pos_iff.mpr (backlund_surrogate_ne_zero_of_one_lt_re (by simpa using hσ))
  have hC : 0 < ‖backlundAuxiliary T n σ‖ :=
    (div_pos (pow_pos hA n) (by norm_num)).trans_le hc
  have ha : AnalyticOnNhd ℂ (backlundAuxiliary T n) (closedBall (σ : ℂ) R) :=
    fun z _ => (differentiable_backlundAuxiliary T n).analyticAt z
  have hj := ha.sum_divisor_le_circleAverage hr hrR (norm_pos_iff.mp hC)
  have hl := Real.log_le_log (div_pos (pow_pos hA n) (by norm_num)) hc
  rw [Real.log_div (pow_pos hA n).ne' (by norm_num), Real.log_pow] at hl
  apply hj.trans
  apply div_le_div_of_nonneg_right _ (Real.log_pos ((one_lt_div hr).mpr hrR)).le
  linarith

/-- The actual horizontal contour inherits the averaged Jensen estimate. -/
theorem abs_im_integral_backlundSurrogate_logDeriv_le_average {T σ r R B a b : ℝ}
    (hσ : 1 < σ) (hr : 0 < r) (hrR : r < R)
    (hab : a ≤ b) (hseg : ∀ x ∈ Icc a b, |x - σ| ≤ r)
    (hne : ∀ x ∈ Icc a b, Backlund.zetaSurrogate ((x : ℂ) + T * I) ≠ 0)
    (hb : ∀ n : ℕ, circleAverage (fun z => Real.log ‖backlundAuxiliary T n z‖) σ R ≤
      (n : ℝ) * B) :
    |(∫ x in a..b, logDeriv Backlund.zetaSurrogate ((x : ℂ) + T * I)).im| ≤
      Real.pi * ((B - Real.log ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) /
        Real.log (R / r)) := by
  have hcont : Continuous (fun x : ℝ => Backlund.zetaSurrogate ((x : ℂ) + T * I)) :=
    Backlund.zetaSurrogate_differentiable.continuous.comp (by fun_prop)
  obtain ⟨L, hL, _, he⟩ := Complex.exists_continuous_log_on_Icc hab hcont.continuousOn hne
    (Complex.exp_log (hne a ⟨le_rfl, hab⟩))
  rw [integral_backlundSurrogate_logDeriv_eq hab hL.continuousOn he, sub_im]
  apply backlund_log_im_sub_le_of_frequent_zeroCount hab hr.le hseg hL.continuousOn he
    (C := Real.log 2 / Real.log (R / r))
  apply (frequently_backlundAuxiliary_centre_lower hσ T).mono
  intro n hc
  have hA : 0 < ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖ :=
    norm_pos_iff.mpr (backlund_surrogate_ne_zero_of_one_lt_re (by simpa using hσ))
  have hC : backlundAuxiliary T n σ ≠ 0 :=
    norm_pos_iff.mp ((div_pos (pow_pos hA n) (by norm_num)).trans_le hc)
  refine ⟨hC, ?_⟩
  have h := (backlundRealZeroCount_le_mass hr.le hC).trans
    (backlundAuxiliaryZeroMass_le_average hσ hr hrR hc (hb n))
  convert h using 1
  ring

end

end PrimeFactorUnimodality
