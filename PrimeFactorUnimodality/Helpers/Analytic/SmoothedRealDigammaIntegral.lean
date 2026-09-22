import PrimeFactorUnimodality.Helpers.Analytic.SmoothedDigammaIntegral
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedDigammaReflection
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaConjugation

/-! # Evaluation of the real-digamma contour pairing

Conjugation averages the forward and reflected shifted digamma series.
The recurrence contributes one left-hand pole, which evaluates to the
Laplace remainder at `s`, and one right-hand pole, which contributes zero.
The argument works on every positive contour strictly left of `s`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set
open scoped ComplexConjugate

private theorem digamma_half_eq_shift_sub {z : ℂ} (hz : 0 < z.re) :
    digamma (z / 2) = digamma (z / 2 + 1) - 2 / z := by
  have hn (n : ℕ) : z / 2 ≠ -(n : ℂ) := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [div_ofNat_re, neg_re, natCast_re] at hre
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hr := digamma_apply_add_one (z / 2) hn
  rw [inv_div] at hr
  linear_combination -hr

private theorem real_digamma_vertical_eq {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ((digamma (((c : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) =
      (1 / 2 : ℂ) * digamma (((c : ℂ) + (t : ℂ) * I) / 2 + 1) +
      (1 / 2 : ℂ) * digamma (((c : ℂ) - (t : ℂ) * I) / 2 + 1) -
      1 / ((c : ℂ) + (t : ℂ) * I) - 1 / ((c : ℂ) - (t : ℂ) * I) := by
  rw [ofReal_re_digamma_eq_average]
  have heq : conj (((c : ℂ) + (t : ℂ) * I) / 2) = ((c : ℂ) - (t : ℂ) * I) / 2 := by
    simp only [map_div₀, map_add, map_mul, conj_ofReal, conj_I, map_ofNat,
      mul_neg, sub_eq_add_neg]
  rw [heq, digamma_half_eq_shift_sub (by simpa using hc),
    digamma_half_eq_shift_sub (by simpa using hc)]
  ring

/-- The real-digamma boundary integral equals the negative trivial-zero series minus `R(s)`. -/
theorem integral_finiteLaplace_mul_re_digamma_eq_remainders
    {f g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M)
    {s : ℂ} {c : ℝ} (hc : 0 < c) (hcs : c < s.re) :
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
      (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) *
      ((digamma (((c : ℂ) + (t : ℂ) * I) / 2)).re : ℂ)) =
      -(∑' n : ℕ, (finiteLaplace f d (s - shiftedGammaPole n) -
        f 0 / (s - shiftedGammaPole n))) - (finiteLaplace f d s - f 0 / s) := by
  let H : ℝ → ℂ := fun t => finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
    f 0 / (s - ((c : ℂ) + (t : ℂ) * I))
  let A : ℝ → ℂ := fun t => H t * digamma (((c : ℂ) + (t : ℂ) * I) / 2 + 1)
  let B : ℝ → ℂ := fun t => H t * digamma (((c : ℂ) - (t : ℂ) * I) / 2 + 1)
  have hH : Integrable H := integrable_finiteLaplace_sub_pole_contour hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hcs
  have hA : Integrable A := integrable_finiteLaplace_mul_digamma_half_add_one hd hM hf hg hh
    hfg hgh hfd hg₀ hgd hbound hc hcs
  have hB : Integrable B := integrable_finiteLaplace_mul_reflected_digamma hd hM hf hg hh
    hfg hgh hfd hg₀ hgd hbound hc hcs
  have hp : Integrable (fun t : ℝ => H t / ((c : ℂ) + (t : ℂ) * I)) := by
    simpa only [sub_zero] using integrable_div_vertical hH (ρ := 0) hc
  have hright : c < (2 * (c : ℂ)).re := by simp; linarith
  have hden (t : ℝ) : (c : ℂ) - (t : ℂ) * I = -((c : ℂ) + (t : ℂ) * I - 2 * c) := by ring
  have hm : Integrable (fun t : ℝ => H t / ((c : ℂ) - (t : ℂ) * I)) := by
    simp_rw [hden, div_neg]
    exact (integrable_div_vertical_of_right hH hright).neg
  have hmzero : (∫ t : ℝ, H t / ((c : ℂ) - (t : ℂ) * I)) = 0 := by
    simp_rw [hden, div_neg]
    rw [integral_neg, integral_finiteLaplace_sub_pole_div_vertical_of_right hd hM hf hg hh
      hfg hgh hfd hg₀ hgd hbound hcs hright, neg_zero]
  have hBzero : (∫ t : ℝ, B t) = 0 :=
    integral_finiteLaplace_mul_reflected_digamma_eq_zero hd hM hf hg hh hfg hgh
      hfd hg₀ hgd hbound hc hcs
  have hsum : Integrable (fun t : ℝ => (1 / 2 : ℂ) * A t + (1 / 2 : ℂ) * B t) :=
    (hA.const_mul _).add (hB.const_mul _)
  have hsub : Integrable (fun t : ℝ => (1 / 2 : ℂ) * A t + (1 / 2 : ℂ) * B t -
      H t / ((c : ℂ) + (t : ℂ) * I)) := hsum.sub hp
  have hsplit : (∫ t : ℝ, H t * ((digamma (((c : ℂ) + (t : ℂ) * I) / 2)).re : ℂ)) =
      (1 / 2 : ℂ) * (∫ t : ℝ, A t) - ∫ t : ℝ, H t / ((c : ℂ) + (t : ℂ) * I) := by
    calc
      _ = ∫ t : ℝ, (1 / 2 : ℂ) * A t + (1 / 2 : ℂ) * B t -
          H t / ((c : ℂ) + (t : ℂ) * I) - H t / ((c : ℂ) - (t : ℂ) * I) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [real_digamma_vertical_eq hc t]
        dsimp [A, B]
        ring
      _ = _ := by
        rw [integral_sub hsub hm, integral_sub hsum hp,
          integral_add (hA.const_mul (1 / 2 : ℂ)) (hB.const_mul (1 / 2 : ℂ)),
          integral_const_mul, integral_const_mul, hBzero, hmzero, mul_zero, add_zero, sub_zero]
  have ha := integral_finiteLaplace_mul_digamma_half_add_one_eq_remainders hd hM hf hg hh
    hfg hgh hfd hg₀ hgd hbound hc hcs
  have hpole := integral_finiteLaplace_sub_pole_div_vertical hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hcs (ρ := 0) hc
  simp only [sub_zero] at hpole
  change (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, H t * _) = _
  rw [hsplit]
  change (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, A t) = _ at ha
  change (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, H t / _) = _ at hpole
  linear_combination (1 / 2 : ℂ) * ha - hpole

end

end PrimeFactorUnimodality
