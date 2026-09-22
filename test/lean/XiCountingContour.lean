import PrimeFactorUnimodality.Helpers.Analytic.BacklundXiLogDerivative
import PrimeFactorUnimodality.Helpers.Analytic.XiHalfContour
import PrimeFactorUnimodality.Helpers.Analytic.XiRegularHeights

/-! # The actual xi counting contour and its regular-height extension

Check real-axis nonvanishing, all multiplicities, the degenerate height-zero
contour, the half-contour orientation and factor of pi, and the continuation
to arbitrary cutoffs. The surrogate decomposition is valid inside the
right half-plane when the particular point is nonzero and not the zeta pole.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter Set
open scoped ComplexConjugate Topology

example : (riemannZeta (1 / 2 : ℂ)).re < 0 := by
  simpa using riemannZeta_re_neg_of_half_le_of_lt_one (σ := (1 / 2 : ℝ)) le_rfl (by norm_num)

example (x : ℝ) : riemannXi (x : ℂ) ≠ 0 := riemannXi_ofReal_ne_zero x

example {T : ℝ} (hT : 0 ≤ T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    RectangleIntegral' (logDeriv riemannXi) (-1) (2 + T * I) = (riemannZeta.N T : ℂ) := by
  convert rectangleIntegral_logDeriv_xi_eq_zeta_N (σ := 2) (by norm_num) hT htop using 1
  norm_num

example : RectangleIntegral' (logDeriv riemannXi) (-1) 2 = 0 := by
  have h := rectangleIntegral_logDeriv_xi_eq_zeta_N (σ := 2) (T := 0) (by norm_num) le_rfl
    (fun _ hz => riemannXi_ne_zero_of_im_eq_zero hz)
  norm_num [riemannZeta.N, riemannZeta.zeroes_sum, riemannZeta.zeroes_rect] at h ⊢
  exact h

example (z : ℂ) : logDeriv riemannXi (conj z) = conj (logDeriv riemannXi z) :=
  logDeriv_riemannXi_conj z

example {σ T : ℝ} (hσ : 1 ≤ σ) (hT : 0 ≤ T)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    Real.pi * riemannZeta.N T = (VIntegral (logDeriv riemannXi) σ 0 T).im -
      (HIntegral (logDeriv riemannXi) (1 / 2) σ T).im :=
  pi_mul_zeta_N_eq_xi_half_contour hσ hT htop

example {T : ℝ} (hT : 0 ≤ T) :
    ∀ᶠ x in 𝓝[>] T, ∀ z : ℂ, z.im = x → riemannXi z ≠ 0 :=
  eventually_xi_horizontal_nonzero hT

example {P B : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hP : ContinuousAt P T) (hB : ContinuousAt B T)
    (h : ∀ x, T < x → (∀ z : ℂ, z.im = x → riemannXi z ≠ 0) →
      |riemannZeta.N x - P x| ≤ B x) :
    |(xiZeroCount T : ℝ) - P T| ≤ B T :=
  xiZeroCount_error_le_of_regular_heights hT hP hB h

example {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hne : riemannZeta s ≠ 0) :
    logDeriv riemannXi s = logDeriv Backlund.zetaSurrogate s -
      (1 / 2 : ℂ) * Real.log Real.pi + (1 / 2 : ℂ) * digamma (s / 2 + 1) :=
  logDeriv_xi_eq_backlundSurrogate hs hs1 hne

example {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s = -logDeriv riemannXi s + 1 / (s - 1) -
      (1 / 2 : ℂ) * Real.log Real.pi + (1 / 2 : ℂ) * digamma (s / 2 + 1) :=
  neg_logDeriv_riemannZeta_eq_xi hs

end

end PrimeFactorUnimodality.Tests
