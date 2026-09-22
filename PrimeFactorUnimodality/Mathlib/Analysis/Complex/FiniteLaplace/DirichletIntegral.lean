/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Inversion
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.VerticalIntegral

/-! # A smoothed Dirichlet series as an absolutely convergent contour integral

Absolute inverse Laplace transformation evaluates every Dirichlet term.
The integrated term norms are summable, so the full series can be
interchanged with the integral. All analytic side conditions are derived
from interval regularity, endpoint conditions, a bound on the second
derivative, and absolute convergence of the Dirichlet series on the line.
-/

namespace Complex

noncomputable section

open MeasureTheory Set

/-- Inversion at `log n`, including `n=0` through the Dirichlet zero-term convention. -/
theorem integral_term_mul_finiteLaplace_sub_pole {f g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M)
    (a : ℕ → ℂ) {s : ℂ} {c : ℝ} (hc : c < s.re) (n : ℕ) :
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
      LSeries.term a ((c : ℂ) + (t : ℂ) * I) n *
        (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
          f 0 / (s - ((c : ℂ) + (t : ℂ) * I)))) =
      finiteLaplaceRemainderSource f d (Real.log n) * LSeries.term a s n := by
  let R : ℝ → ℂ := fun t => finiteLaplace f d (s - c + (t : ℂ) * I) -
    f 0 / (s - c + (t : ℂ) * I)
  have hinv := integral_finiteLaplace_sub_pole_vertical hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound (s := s - c) (by simpa using sub_pos.mpr hc) (Real.log n)
  have hflip : (∫ t : ℝ, exp (-((t : ℂ) * I) * (Real.log n : ℂ)) * R (-t)) =
      ∫ t : ℝ, exp ((t : ℂ) * I * (Real.log n : ℂ)) * R t := by
    simpa only [ofReal_neg, neg_mul, Function.comp_def] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
        (Homeomorph.neg ℝ).measurableEmbedding
        (fun t : ℝ => exp ((t : ℂ) * I * (Real.log n : ℂ)) * R t)
  have hterm (t : ℝ) :
      LSeries.term a ((c : ℂ) + (t : ℂ) * I) n *
        (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
          f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) =
      LSeries.term a (c : ℂ) n *
        (exp (-((t : ℂ) * I) * (Real.log n : ℂ)) * R (-t)) := by
    rw [← LSeries.term_mul_exp a (c : ℂ) ((t : ℂ) * I) n]
    simp only [R, ofReal_neg, neg_mul, sub_eq_add_neg, neg_add, add_assoc, mul_assoc]
  simp_rw [hterm]
  rw [integral_const_mul, ← mul_assoc, mul_comm _ (LSeries.term a (c : ℂ) n), mul_assoc,
    hflip, hinv]
  rw [← mul_assoc, LSeries.term_mul_exp]
  simp only [add_sub_cancel, mul_comm]

/-- Absolute smoothing identity on any line where the underlying Dirichlet series converges. -/
theorem tsum_remainderSource_mul_term_eq_integral {f g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M)
    {a : ℕ → ℂ} {s : ℂ} {c : ℝ} (hc : c < s.re) (ha : LSeriesSummable a (c : ℂ)) :
    (∑' n : ℕ, finiteLaplaceRemainderSource f d (Real.log n) * LSeries.term a s n) =
      (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
        LSeries a ((c : ℂ) + (t : ℂ) * I) *
          (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
            f 0 / (s - ((c : ℂ) + (t : ℂ) * I)))) := by
  have hvertical := integrable_finiteLaplace_sub_pole_vertical hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound (s := s - c) (by simpa using sub_pos.mpr hc)
  have hK : Integrable (fun t : ℝ =>
      finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) := by
    simpa [sub_sub, sub_eq_add_neg, add_assoc, add_comm] using hvertical.comp_neg
  calc
    _ = ∑' n : ℕ, (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
        LSeries.term a ((c : ℂ) + (t : ℂ) * I) n *
          (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
            f 0 / (s - ((c : ℂ) + (t : ℂ) * I)))) :=
      tsum_congr fun n => (integral_term_mul_finiteLaplace_sub_pole hd hM hf hg hh hfg hgh
        hfd hg₀ hgd hbound a hc n).symm
    _ = _ := by rw [tsum_mul_left, LSeries.tsum_integral_term_vertical_mul ha hK]

end

end Complex
