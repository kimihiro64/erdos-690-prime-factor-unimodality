import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiZeroContribution
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Summability

set_option autoImplicit false

/-! # Absolute convergence of compactly smoothed xi zero contributions

The pole-subtracted complex Laplace transform is summable over the actual
xi divisor with multiplicity. When the value of the weight at zero is real,
the real parts of the full transform are also absolutely summable. Both
statements cover every complex evaluation point, not just `Re(s)>1`.
They supply convergence for the smoothed explicit formula, not the formula
itself or its eventual numerical error estimate.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Set

private theorem xi_divisor_bounded_finite (R : ℝ) :
    {p : RiemannXiDivisorZeroIndex | ‖riemannXiDivisorZeroValue p‖ ≤ R}.Finite :=
  Hadamard.divisorZeroIndex₀_norm_le_finite
    (f := riemannXi) (U := Set.univ) (B := R) (by simp)

/-- Inverse-square summability is preserved after shifting by any complex point. -/
theorem summable_xi_divisor_shift_inv_sq (s : ℂ) :
    Summable (fun p : RiemannXiDivisorZeroIndex => ‖s - riemannXiDivisorZeroValue p‖⁻¹ ^ 2) :=
  summable_norm_sub_inv_sq riemannXiDivisorZeroValue xi_divisor_bounded_finite
    summable_riemannXiDivisorZero_norm_inv_sq s

/-- Real resolvent contributions are absolutely summable on every vertical line. -/
theorem summable_re_xi_divisor_resolvent (s : ℂ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      (1 / (s - riemannXiDivisorZeroValue p)).re) := by
  have hmajor := (summable_xi_divisor_shift_inv_sq s).mul_left (|s.re| + 1)
  apply hmajor.of_norm_bounded
  intro p
  let ρ := riemannXiDivisorZeroValue p
  obtain ⟨hβ₀, hβ₁⟩ := riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)
  have hnum : |s.re - ρ.re| ≤ |s.re| + 1 := by
    have h := abs_sub s.re ρ.re
    have hb : |ρ.re| ≤ 1 := (abs_of_nonneg hβ₀).le.trans hβ₁
    linarith
  change ‖(1 / (s - ρ)).re‖ ≤ (|s.re| + 1) * ‖s - ρ‖⁻¹ ^ 2
  rw [Real.norm_eq_abs, one_div, inv_re, abs_div, abs_of_nonneg (normSq_nonneg _),
    sub_re, normSq_eq_norm_sq]
  calc
    _ ≤ (|s.re| + 1) / ‖s - ρ‖ ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = _ := by rw [div_eq_mul_inv, inv_pow]

/-- The complex Laplace remainder is summable over every xi zero with its multiplicity. -/
theorem summable_xi_finiteLaplace_sub_pole {f g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t)
    (hgh : ∀ t ∈ Ioo 0 d, HasDerivAt g (h t) t)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ t ∈ Icc 0 d, ‖h t‖ ≤ M) (s : ℂ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      finiteLaplace f d (s - riemannXiDivisorZeroValue p) -
        f 0 / (s - riemannXiDivisorZeroValue p)) :=
  summable_finiteLaplace_sub_pole riemannXiDivisorZeroValue xi_divisor_bounded_finite
    summable_riemannXiDivisorZero_norm_inv_sq
    (fun p => (riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)).2)
    hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound s

/-- With a real endpoint value, the full real zero sum converges absolutely at every point. -/
theorem summable_re_xi_finiteLaplace {f g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t)
    (hgh : ∀ t ∈ Ioo 0 d, HasDerivAt g (h t) t)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ t ∈ Icc 0 d, ‖h t‖ ≤ M) (hf₀ : (f 0).im = 0) (s : ℂ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      (finiteLaplace f d (s - riemannXiDivisorZeroValue p)).re) := by
  have hrem := summable_xi_finiteLaplace_sub_pole hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound s
  have hreal := (Complex.hasSum_re hrem.hasSum).summable
  have hpole := (summable_re_xi_divisor_resolvent s).mul_left (f 0).re
  apply (hreal.add hpole).congr
  intro p
  simp only [sub_re, div_eq_mul_inv, mul_re, hf₀, zero_mul, sub_zero, one_mul]
  ring

end

end PrimeFactorUnimodality
