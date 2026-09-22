import PrimeFactorUnimodality.Helpers.Analytic.SmoothedExplicitFormula
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaBoundary

set_option autoImplicit false

/-! # Nonzero smoothing, absolute inversion, and the prime contour identity

The cubic weight equals one at zero and vanishes at one. Its second
derivative at zero is nonzero; it therefore tests that the formalization
does not require a twice continuously differentiable zero extension.
The prime and evaluated xi contour identities are tested at every height
on real part two, together with poles off the critical line. The gamma
pairing is tested below real part one, and the assembled explicit formula
is tested at every point of its proved right-half-plane domain. The full
gamma boundary identity is tested throughout `Re(s)>1/2`, together with
vanishing of right-hand poles at arbitrary heights.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology

private def weight (u : ℝ) : ℝ := if u ≤ 1 then 1 - 3 * u ^ 2 + 2 * u ^ 3 else 0
private def weight₁ (u : ℝ) : ℂ := -6 * (u : ℂ) + 6 * (u : ℂ) ^ 2
private def weight₂ (u : ℝ) : ℂ := -6 + 12 * (u : ℂ)

private theorem weight_continuous : Continuous weight := by
  apply continuous_if_le continuous_id continuous_const
    (by fun_prop) continuous_const.continuousOn
  intro u hu
  change u = 1 at hu
  norm_num [hu]

private theorem weight_tail (u : ℝ) (hu : 1 < u) : weight u = 0 := by
  simp [weight, not_le.mpr hu]

private theorem weight_deriv (u : ℝ) (hu : u ∈ Ioo 0 1) :
    HasDerivAt (fun u => (weight u : ℂ)) (weight₁ u) u := by
  have ht := (hasDerivAt_id u).ofReal_comp
  have hp := ((hasDerivAt_const u (1 : ℂ)).sub ((ht.pow 2).const_mul 3)).add
    ((ht.pow 3).const_mul 2)
  have hp' : HasDerivAt (fun u : ℝ => (1 : ℂ) - 3 * (u : ℂ) ^ 2 + 2 * (u : ℂ) ^ 3)
      (weight₁ u) u := by
    convert hp using 1
    · funext x
      rfl
    · norm_num [weight₁]
      ring
  apply hp'.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hu.2] with x hx
  simp [weight, (mem_Iio.mp hx).le]

private theorem weight₁_deriv (u : ℝ) : HasDerivAt weight₁ (weight₂ u) u := by
  have ht := (hasDerivAt_id u).ofReal_comp
  convert (ht.const_mul (-6)).add ((ht.pow 2).const_mul 6) using 1
  · funext x
    rfl
  · norm_num [weight₂]
    ring

private theorem weight₂_bound (u : ℝ) (hu : u ∈ Icc 0 1) : ‖weight₂ u‖ ≤ 6 := by
  have heq : weight₂ u = ((-6 + 12 * u : ℝ) : ℂ) := by simp [weight₂]
  rw [heq, norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩

example : weight 0 = 1 ∧ weight 1 = 0 ∧ weight₂ 0 = -6 := by norm_num [weight, weight₂]

example : finiteLaplaceRemainderSource (fun u => (weight u : ℂ)) 1 2 = -1 := by
  norm_num [finiteLaplaceRemainderSource, weight]

example (s : ℂ) (hs : 0 < s.re) :
    (1 / (2 * (Real.pi : ℂ))) *
      (∫ t : ℝ, exp ((t : ℂ) * I * 2) *
        (finiteLaplace (fun u => (weight u : ℂ)) 1 (s + (t : ℂ) * I) -
          1 / (s + (t : ℂ) * I))) = -exp (-s * 2) := by
  have h := integral_finiteLaplace_sub_pole_vertical (f := fun u => (weight u : ℂ))
    (g := weight₁) (h := weight₂) (M := 6) (d := 1)
    (by norm_num) (by norm_num)
    (Complex.continuous_ofReal.comp weight_continuous).continuousOn
    (by unfold weight₁; fun_prop) (by unfold weight₂; fun_prop) weight_deriv
    (fun u _ => weight₁_deriv u)
    (by norm_num [weight]) (by norm_num [weight₁]) (by norm_num [weight₁])
    weight₂_bound hs 2
  have hzero : (weight 0 : ℂ) = 1 := by norm_num [weight]
  have hsource : finiteLaplaceRemainderSource (fun u => (weight u : ℂ)) 1 2 = -1 := by
    norm_num [finiteLaplaceRemainderSource, weight]
  simpa only [hzero, hsource, ofReal_ofNat, mul_neg, mul_one] using h

example (y : ℝ) :
    smoothedVonMangoldt weight ((2 : ℂ) + y * I) -
      (-deriv riemannZeta ((2 : ℂ) + y * I) / riemannZeta ((2 : ℂ) + y * I)) =
      (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
        (-deriv riemannZeta ((3 / 2 : ℂ) + (t : ℂ) * I) /
          riemannZeta ((3 / 2 : ℂ) + (t : ℂ) * I)) *
          (finiteLaplace (fun u => (weight u : ℂ)) 1
              (((2 : ℂ) + y * I) - ((3 / 2 : ℂ) + (t : ℂ) * I)) -
            1 / (((2 : ℂ) + y * I) - ((3 / 2 : ℂ) + (t : ℂ) * I)))) := by
  have h := smoothedVonMangoldt_sub_logDeriv_eq_integral (f := weight) (g := weight₁)
    (h := weight₂) (d := 1) (M := 6) (s := (2 : ℂ) + y * I) (c := 3 / 2)
    (by norm_num) (by norm_num) weight_continuous.continuousOn
    (by unfold weight₁; fun_prop) (by unfold weight₂; fun_prop) weight_deriv
    (fun u _ => weight₁_deriv u)
    (by norm_num [weight]) (by norm_num [weight₁]) (by norm_num [weight₁])
    weight₂_bound weight_tail (by norm_num) (by norm_num)
  simpa only [weight, ite_true, show (0 : ℝ) ≤ 1 by norm_num, zero_pow (by norm_num : 2 ≠ 0),
    zero_pow (by norm_num : 3 ≠ 0), mul_zero, sub_zero, add_zero, ofReal_one, one_mul,
    ofReal_div, ofReal_ofNat] using h

example (y v : ℝ) :
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
      (finiteLaplace (fun u => (weight u : ℂ)) 1
          (((2 : ℂ) + y * I) - ((3 / 2 : ℂ) + (t : ℂ) * I)) -
        1 / (((2 : ℂ) + y * I) - ((3 / 2 : ℂ) + (t : ℂ) * I))) /
      (((3 / 2 : ℂ) + (t : ℂ) * I) - ((3 / 4 : ℂ) + v * I))) =
      finiteLaplace (fun u => (weight u : ℂ)) 1
          (((2 : ℂ) + y * I) - ((3 / 4 : ℂ) + v * I)) -
        1 / (((2 : ℂ) + y * I) - ((3 / 4 : ℂ) + v * I)) := by
  have h := integral_finiteLaplace_sub_pole_div_vertical
    (f := fun u => (weight u : ℂ)) (g := weight₁) (h := weight₂) (d := 1) (M := 6)
    (s := (2 : ℂ) + y * I) (c := 3 / 2) (ρ := (3 / 4 : ℂ) + v * I)
    (by norm_num) (by norm_num)
    (Complex.continuous_ofReal.comp weight_continuous).continuousOn
    (by unfold weight₁; fun_prop) (by unfold weight₂; fun_prop) weight_deriv
    (fun u _ => weight₁_deriv u)
    (by norm_num [weight]) (by norm_num [weight₁]) (by norm_num [weight₁])
    weight₂_bound (by norm_num) (by norm_num)
  have hzero : (weight 0 : ℂ) = 1 := by norm_num [weight]
  simpa only [hzero, ofReal_div, ofReal_ofNat] using h

example (y : ℝ) :
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
      (finiteLaplace (fun u => (weight u : ℂ)) 1
          (((2 : ℂ) + y * I) - ((3 / 2 : ℂ) + (t : ℂ) * I)) -
        1 / (((2 : ℂ) + y * I) - ((3 / 2 : ℂ) + (t : ℂ) * I))) *
        logDeriv riemannXi ((3 / 2 : ℂ) + (t : ℂ) * I)) =
      ∑' p : RiemannXiDivisorZeroIndex,
        (finiteLaplace (fun u => (weight u : ℂ)) 1
            (((2 : ℂ) + y * I) - riemannXiDivisorZeroValue p) -
          1 / (((2 : ℂ) + y * I) - riemannXiDivisorZeroValue p)) := by
  have h := integral_finiteLaplace_mul_logDeriv_riemannXi_eq_remainders
    (f := fun u => (weight u : ℂ)) (g := weight₁) (h := weight₂) (d := 1) (M := 6)
    (s := (2 : ℂ) + y * I) (c := 3 / 2)
    (by norm_num) (by norm_num)
    (Complex.continuous_ofReal.comp weight_continuous).continuousOn
    (by unfold weight₁; fun_prop) (by unfold weight₂; fun_prop) weight_deriv
    (fun u _ => weight₁_deriv u)
    (by norm_num [weight]) (by norm_num [weight₁]) (by norm_num [weight₁])
    weight₂_bound (by norm_num) (by norm_num)
  have hzero : (weight 0 : ℂ) = 1 := by norm_num [weight]
  simpa only [hzero, ofReal_div, ofReal_ofNat] using h

example (y : ℝ) :
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
      (finiteLaplace (fun u => (weight u : ℂ)) 1
          (((3 / 4 : ℂ) + y * I) - ((1 / 4 : ℂ) + (t : ℂ) * I)) -
        1 / (((3 / 4 : ℂ) + y * I) - ((1 / 4 : ℂ) + (t : ℂ) * I))) *
        digamma (((1 / 4 : ℂ) + (t : ℂ) * I) / 2 + 1)) =
      -2 * ∑' n : ℕ, (finiteLaplace (fun u => (weight u : ℂ)) 1
          (((3 / 4 : ℂ) + y * I) + 2 * ((n : ℂ) + 1)) -
        1 / (((3 / 4 : ℂ) + y * I) + 2 * ((n : ℂ) + 1))) := by
  have h := integral_finiteLaplace_mul_digamma_half_add_one_eq_remainders
    (f := fun u => (weight u : ℂ)) (g := weight₁) (h := weight₂) (d := 1) (M := 6)
    (s := (3 / 4 : ℂ) + y * I) (c := 1 / 4)
    (by norm_num) (by norm_num)
    (Complex.continuous_ofReal.comp weight_continuous).continuousOn
    (by unfold weight₁; fun_prop) (by unfold weight₂; fun_prop) weight_deriv
    (fun u _ => weight₁_deriv u)
    (by norm_num [weight]) (by norm_num [weight₁]) (by norm_num [weight₁])
    weight₂_bound (by norm_num) (by norm_num)
  have hzero : (weight 0 : ℂ) = 1 := by norm_num [weight]
  simpa only [hzero, ofReal_div, ofReal_one, ofReal_ofNat, shiftedGammaPole, sub_neg_eq_add] using h

example (s : ℂ) (hs : 1 < s.re) :
    smoothedVonMangoldt weight s - (-deriv riemannZeta s / riemannZeta s) =
      (finiteLaplace (fun u => (weight u : ℂ)) 1 (s - 1) - 1 / (s - 1)) -
      (∑' p : RiemannXiDivisorZeroIndex,
        (finiteLaplace (fun u => (weight u : ℂ)) 1 (s - riemannXiDivisorZeroValue p) -
          1 / (s - riemannXiDivisorZeroValue p))) -
      ∑' n : ℕ, (finiteLaplace (fun u => (weight u : ℂ)) 1 (s + 2 * ((n : ℂ) + 1)) -
        1 / (s + 2 * ((n : ℂ) + 1))) := by
  have h := smoothedVonMangoldt_explicitFormula_of_one_lt_re
    (f := weight) (g := weight₁) (h := weight₂) (d := 1) (M := 6)
    (by norm_num) (by norm_num) weight_continuous.continuousOn
    (by unfold weight₁; fun_prop) (by unfold weight₂; fun_prop) weight_deriv
    (fun u _ => weight₁_deriv u)
    (by norm_num [weight]) (by norm_num [weight₁]) (by norm_num [weight₁])
    weight₂_bound weight_tail hs
  have hzero : (weight 0 : ℂ) = 1 := by norm_num [weight]
  simpa only [hzero, one_mul, shiftedGammaPole, sub_neg_eq_add] using h

example (y v : ℝ) :
    (∫ t : ℝ, (finiteLaplace (fun u => (weight u : ℂ)) 1
        (((3 / 4 : ℂ) + y * I) - ((1 / 2 : ℂ) + (t : ℂ) * I)) -
      1 / (((3 / 4 : ℂ) + y * I) - ((1 / 2 : ℂ) + (t : ℂ) * I))) /
      (((1 / 2 : ℂ) + (t : ℂ) * I) - ((1 : ℂ) + v * I))) = 0 := by
  have h := integral_finiteLaplace_sub_pole_div_vertical_of_right
    (f := fun u => (weight u : ℂ)) (g := weight₁) (h := weight₂) (d := 1) (M := 6)
    (s := (3 / 4 : ℂ) + y * I) (c := 1 / 2) (ρ := (1 : ℂ) + v * I)
    (by norm_num) (by norm_num)
    (Complex.continuous_ofReal.comp weight_continuous).continuousOn
    (by unfold weight₁; fun_prop) (by unfold weight₂; fun_prop) weight_deriv
    (fun u _ => weight₁_deriv u)
    (by norm_num [weight]) (by norm_num [weight₁]) (by norm_num [weight₁])
    weight₂_bound (by norm_num) (by norm_num)
  have hzero : (weight 0 : ℂ) = 1 := by norm_num [weight]
  simpa only [hzero, ofReal_div, ofReal_one, ofReal_ofNat] using h

example (s : ℂ) (hs : 1 / 2 < s.re) :
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, smoothedGammaIntegrand weight₂ 1 s t) +
      finiteLaplace weight₂ 1 s / s ^ 2 =
      -(∑' n : ℕ, (finiteLaplace (fun u => (weight u : ℂ)) 1 (s + 2 * ((n : ℂ) + 1)) -
        1 / (s + 2 * ((n : ℂ) + 1)))) := by
  have h := smoothedGammaRemainder_eq_neg_trivialZeroSum
    (f := fun u => (weight u : ℂ)) (g := weight₁) (h := weight₂) (d := 1) (M := 6)
    (by norm_num) (by norm_num)
    (Complex.continuous_ofReal.comp weight_continuous).continuousOn
    (by unfold weight₁; fun_prop) (by unfold weight₂; fun_prop) weight_deriv
    (fun u _ => weight₁_deriv u)
    (by norm_num [weight]) (by norm_num [weight₁]) (by norm_num [weight₁])
    weight₂_bound hs
  have hzero : (weight 0 : ℂ) = 1 := by norm_num [weight]
  simpa only [smoothedGammaRemainder, hzero, shiftedGammaPole, sub_neg_eq_add] using h

end

end PrimeFactorUnimodality.Tests
