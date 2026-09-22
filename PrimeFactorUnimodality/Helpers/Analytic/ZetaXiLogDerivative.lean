import Mathlib.NumberTheory.LSeries.Nonvanishing
import PrimeFactorUnimodality.Helpers.Analytic.DigammaExplicitBounds
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.CompletedXi

set_option autoImplicit false

/-! # The xi logarithmic derivative with an explicit gamma term

Identify the entire xi function with its gamma product on `Re(s) > 1` and
differentiate there. Combining the identity with the explicit digamma bound
leaves exactly the xi logarithmic derivative to be estimated by its zeros.

The xi normalization is Matteo Cipollina's Apache-2.0 `CompletedXi` module
in `kimihiro64/PrimeNumberTheoremAnd` at revision
`f6147e7572ab3abe5428101bc0b13627bcb005df`. The product/log-derivative algebra
follows `Kadiri.logDeriv_completedZetaFactor` and
`Kadiri.neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv` in that revision's
`IEANTN/HadamardLogDerivative`. This small closure uses Mathlib's current
`logDeriv_fun_mul` API and does not import that module or assume a Hadamard
formula. Its source commit is `f60a50a93cfc7d205db1c3d1653a922effb27375`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter
open scoped Topology

private def xiPiFactor (s : ℂ) : ℂ :=
  Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))

private theorem xiPiFactor_eq (s : ℂ) :
    xiPiFactor s = (Real.pi : ℂ) ^ (-s / 2) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero),
    ← ofReal_log Real.pi_pos.le]
  dsimp [xiPiFactor]
  congr 1
  ring

/-- Product representation using the pole-cancelling shifted gamma function. -/
theorem riemannXi_eq_shifted_gamma_product {s : ℂ} (hs : 1 < s.re) :
    riemannXi s = (s - 1) * Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ)) *
      Gamma (s / 2 + 1) * riemannZeta s := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hcomp : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _
      (Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs))]
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1, hcomp, Gammaℝ_def,
    Gamma_add_one _ (div_ne_zero hs0 (by norm_num))]
  change s * (s - 1) * (_ * _ * _) / 2 =
    (s - 1) * xiPiFactor s * (s / 2 * _) * _
  rw [xiPiFactor_eq]
  ring

/-- Exact logarithmic-derivative identity, before estimating the xi zero contribution. -/
theorem neg_logDeriv_riemannZeta_eq_xi {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      -logDeriv riemannXi s + 1 / (s - 1) - (1 / 2 : ℂ) * Real.log Real.pi +
        (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  let F : ℂ → ℂ := fun z => (z - 1) * xiPiFactor z * Gamma (z / 2 + 1) * riemannZeta z
  have heq : riemannXi =ᶠ[𝓝 s] F := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact riemannXi_eq_shifted_gamma_product hz
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hΓpos : 0 < (s / 2 + 1).re := by
    simp only [add_re, div_ofNat_re, one_re]
    linarith
  have hΓdiff : ∀ n : ℕ, s / 2 + 1 ≠ -(n : ℂ) := by
    intro n hn
    have h := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hΓ := Gamma_ne_zero_of_re_pos hΓpos
  have hζ := riemannZeta_ne_zero_of_one_le_re hs.le
  have hπ : xiPiFactor s ≠ 0 := exp_ne_zero _
  have hdπ : DifferentiableAt ℂ xiPiFactor s := by unfold xiPiFactor; fun_prop
  have hdΓ : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2 + 1)) s :=
    (differentiableAt_Gamma _ hΓdiff).comp s (by fun_prop)
  have hπlog : logDeriv xiPiFactor s = -(1 / 2 : ℂ) * Real.log Real.pi := by
    unfold xiPiFactor
    rw [show (fun z : ℂ => Complex.exp (-(z / 2) * (Real.log Real.pi : ℂ))) =
      Complex.exp ∘ (fun z : ℂ => -(z / 2) * (Real.log Real.pi : ℂ)) by rfl,
      logDeriv_comp]
    · simp
    · fun_prop
    · fun_prop
  have hΓlog : logDeriv (fun z : ℂ => Gamma (z / 2 + 1)) s =
      (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
    rw [show (fun z : ℂ => Gamma (z / 2 + 1)) =
      Gamma ∘ (fun z : ℂ => z / 2 + 1) by rfl, logDeriv_comp]
    · simp [digamma_def]
      ring
    · exact differentiableAt_Gamma _ hΓdiff
    · fun_prop
  have hF : logDeriv F s = 1 / (s - 1) - (1 / 2 : ℂ) * Real.log Real.pi +
      (1 / 2 : ℂ) * digamma (s / 2 + 1) + deriv riemannZeta s / riemannZeta s := by
    dsimp only [F]
    rw [logDeriv_fun_mul (f := fun z => (z - 1) * xiPiFactor z * Gamma (z / 2 + 1))
      (g := riemannZeta) s (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hs1) hπ) hΓ)
      hζ (((differentiableAt_id.sub_const 1).mul hdπ).mul hdΓ)
      (differentiableAt_riemannZeta hs1)]
    rw [logDeriv_fun_mul (f := fun z => (z - 1) * xiPiFactor z)
      (g := fun z => Gamma (z / 2 + 1)) s (mul_ne_zero (sub_ne_zero.mpr hs1) hπ) hΓ
      ((differentiableAt_id.sub_const 1).mul hdπ) hdΓ]
    rw [logDeriv_fun_mul (f := fun z => z - 1) (g := xiPiFactor) s (sub_ne_zero.mpr hs1) hπ
      (differentiableAt_id.sub_const 1) hdπ, hπlog, hΓlog]
    simp [logDeriv_apply]
    ring
  have hxi := (logDeriv_congr_nhds heq).eq_of_nhds
  rw [hxi, hF]
  ring

/-- The remaining analytic task is now a lower bound on the xi logarithmic derivative. -/
theorem re_neg_logDeriv_riemannZeta_le_xi {s : ℂ} (hs : 1 < s.re) (hs₂ : s.re ≤ 2) :
    (-deriv riemannZeta s / riemannZeta s).re ≤
      -(logDeriv riemannXi s).re + (1 / (s - 1)).re +
        ((1 / 2 : ℝ) * Real.log (|s.im| / 2 + 3) + 1 / 2 -
          (1 / 2 : ℝ) * Real.log Real.pi) := by
  have h := re_zeta_gamma_factor_le_vertical (zero_lt_one.trans hs).le hs₂
  rw [neg_logDeriv_riemannZeta_eq_xi hs]
  simp only [neg_mul, add_re, sub_re, neg_re] at *
  linarith

end

end PrimeFactorUnimodality
