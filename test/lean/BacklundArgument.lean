import PrimeFactorUnimodality.Helpers.Analytic.BacklundArgumentIntegral

/-! # Continuous logarithms and the horizontal Backlund estimate

Check arbitrary initial logarithms, degenerate intervals, signed phases,
actual finite crossing counts, and removal of the finite-power error terms.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Metric Real Set

example {a b : ℝ} (hab : a ≤ b) : |(0 : ℝ) - 0| ≤ Real.pi := by
  have h : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc a b) := continuousOn_const
  simpa using h.abs_sub_le_card_add_one_mul_pi_of_cos_eq_zero hab ∅ (by simp)

example {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hz : {x ∈ Icc a b | Real.cos (f x) = 0}.Finite) :
    |f b - f a| ≤ ({x ∈ Icc a b | Real.cos (f x) = 0}.ncard + 1 : ℝ) * Real.pi :=
  hf.abs_sub_le_ncard_add_one_mul_pi_of_cos_eq_zero hab hz

example {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (s : Finset ℝ) (hs : ∀ x ∈ Icc a b, Real.cos (f x) = 0 → x ∈ s) :
    |(-f b) - (-f a)| ≤ (s.card + 1 : ℝ) * Real.pi :=
  hf.neg.abs_sub_le_card_add_one_mul_pi_of_cos_eq_zero hab s (by simpa using hs)

example (a : ℝ) (c : ℂ) : ∃ L : ℝ → ℂ, Continuous L ∧ L a = c ∧
    ∀ x ∈ Icc a a, Complex.exp (L x) = Complex.exp c :=
  Complex.exists_continuous_log_on_Icc le_rfl continuousOn_const
    (fun _ _ => Complex.exp_ne_zero c) rfl

example {T σ r a b : ℝ} {n : ℕ} {L : ℝ → ℂ}
    (hab : a ≤ b) (hr : 0 ≤ r) (hn : 0 < n)
    (hseg : ∀ x ∈ Icc a b, |x - σ| ≤ r) (hL : ContinuousOn L (Icc a b))
    (he : ∀ x ∈ Icc a b, Complex.exp (L x) = Backlund.zetaSurrogate ((x : ℂ) + T * I))
    (hc : backlundAuxiliary T n σ ≠ 0) :
    |(L b).im - (L a).im| ≤ (backlundRealZeroCount T n σ r + 1 : ℝ) * Real.pi / n :=
  backlund_log_im_sub_le_zeroCount hab hr hn hseg hL he hc

example {T σ r R M a b : ℝ} {L : ℝ → ℂ}
    (hσ : 1 < σ) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hab : a ≤ b) (hseg : ∀ x ∈ Icc a b, |x - σ| ≤ r) (hL : ContinuousOn L (Icc a b))
    (he : ∀ x ∈ Icc a b, Complex.exp (L x) = Backlund.zetaSurrogate ((x : ℂ) + T * I))
    (hp : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    |(L b).im - (L a).im| ≤ Real.pi *
      (Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) / Real.log (R / r)) :=
  backlund_log_im_sub_le_jensen hσ hr hrR hM hab hseg hL he hp hm

example {T a b : ℝ} {L : ℝ → ℂ} (hab : a ≤ b) (hL : ContinuousOn L (Icc a b))
    (he : ∀ x ∈ Icc a b, Complex.exp (L x) = Backlund.zetaSurrogate ((x : ℂ) + T * I)) :
    ∫ x in a..b, logDeriv Backlund.zetaSurrogate ((x : ℂ) + T * I) = L b - L a :=
  integral_backlundSurrogate_logDeriv_eq hab hL he

example {T σ r R M a b : ℝ}
    (hσ : 1 < σ) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hab : a ≤ b) (hseg : ∀ x ∈ Icc a b, |x - σ| ≤ r)
    (hne : ∀ x ∈ Icc a b, Backlund.zetaSurrogate ((x : ℂ) + T * I) ≠ 0)
    (hp : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    |(∫ x in a..b, logDeriv Backlund.zetaSurrogate ((x : ℂ) + T * I)).im| ≤ Real.pi *
      (Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) / Real.log (R / r)) :=
  abs_im_integral_backlundSurrogate_logDeriv_le hσ hr hrR hM hab hseg hne hp hm

end

end PrimeFactorUnimodality.Tests
