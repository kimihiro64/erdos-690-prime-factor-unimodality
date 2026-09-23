import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Parameters

/-! # Height-uniform R6 interfaces, boundaries and actual consumers -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Finset Real

example : KadiriHighRegion 69 25000000 := by
  exact PrimeFactorUnimodality.kadiriHighRegion_reduced_initial

example {T : ℝ} (hT : 25000000 ≤ T) :
    (17034 / 1000 : ℝ) ≤ log T := by
  exact PrimeFactorUnimodality.kadiriSix_log_height_ge hT

example {T : ℝ} (hT : 25000000 ≤ T) :
    (99 / 5 : ℝ) ≤ log (16 * T + 100000) := by
  exact PrimeFactorUnimodality.kadiriSix_log_harmonic_ge hT

example {T r : ℝ} (hT : 25000000 ≤ T) (hr : 6 ≤ r) :
    0 < KadiriEndpointRow.scale r T ∧
      KadiriEndpointRow.scale r T ≤ (98 / 10000 : ℝ) := by
  exact PrimeFactorUnimodality.kadiriSix_scale_bounds hT hr

example {T R : ℝ} (hT : 25000000 ≤ T) (hR : 13 / 2 ≤ R) :
    (9922 / 10000 : ℝ) ≤ kadiriSixRow.sigma R T 16 ∧
      kadiriSixRow.sigma R T 16 ≤ 1 := by
  exact PrimeFactorUnimodality.kadiriSix_sigma_bounds hT hR

example {η σ : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 98 / 10000)
    (hσ : 9922 / 10000 ≤ σ)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0)
    (hg' : kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ)) :
    (437 / 1000 : ℝ) ≤ kadiriKappa₂ (185573 / 100000) η (2 * σ - 1) (62 / 100) ∧
      (437 / 1000 : ℝ) ≤ kadiriKappa₃ (185573 / 100000) η (2 * σ - 1) (62 / 100) := by
  exact PrimeFactorUnimodality.kadiriSix_kappa_bounds hη hη' hσ hg hg' hm

example {T R r : ℝ} (hT : 25000000 ≤ T) (hR : 13 / 2 ≤ R) (hr : 6 ≤ r)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100))
    (hcor : kadiriSixRow.correction R r T 16 mossinghoffTrudgianCoefficient ≤ 0)
    (hlo : kadiriBootstrapLogCoefficient (185573 / 100000) (437 / 1000)
      (Finset.range 17) mossinghoffTrudgianCoefficient / r ≤
        kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1)
          (kadiriBootstrapLowerArgument R r 16 100000 T))
    (hhi : kadiriBootstrapLogCoefficient (185573 / 100000) (437 / 1000)
      (Finset.range 17) mossinghoffTrudgianCoefficient / r ≤
        kadiriTransformGapClosedForm (185573 / 100000) 1 (mossinghoffTrudgianCoefficient 1) 1) :
    kadiriSixRow.Valid R r T 16 mossinghoffTrudgianCoefficient := by
  exact PrimeFactorUnimodality.kadiriSix_valid hT hR hr hg hm hd he hcor hlo hhi

example : 0 < KadiriEndpointRow.scale 6 25000000 ∧
    KadiriEndpointRow.scale 6 25000000 ≤ (98 / 10000 : ℝ) :=
  kadiriSix_scale_bounds le_rfl le_rfl

example : (9922 / 10000 : ℝ) ≤ kadiriSixRow.sigma (13 / 2) 25000000 16 ∧
    kadiriSixRow.sigma (13 / 2) 25000000 16 ≤ 1 :=
  kadiriSix_sigma_bounds le_rfl le_rfl

example : 0 < KadiriEndpointRow.scale 6 (25000000 + 1 / 2) ∧
    KadiriEndpointRow.scale 6 (25000000 + 1 / 2) ≤ (98 / 10000 : ℝ) :=
  kadiriSix_scale_bounds (by norm_num) le_rfl

example : kadiriSixRow.kappa = (437 / 1000 : ℝ) := rfl

end

end PrimeFactorUnimodality.Tests
