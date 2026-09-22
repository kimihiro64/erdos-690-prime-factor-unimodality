import PrimeFactorUnimodality.Helpers.Analytic.DigammaHadamard
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedXiRemainder
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.PairedSeries

/-! # Entire paired sums over nontrivial and trivial zeros

Both zero families satisfy local finiteness and inverse-square summability.
The generic closed-ball majorant therefore gives entire paired sums with
actual xi multiplicities. No hypothesis about zero locations beyond the
closed critical strip is used.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Set

/-- The xi sum paired with its reciprocal constants, preserving multiplicity. -/
def smoothedXiPairedSum (f : ℝ → ℂ) (d : ℝ) (s : ℂ) : ℂ :=
  ∑' p : RiemannXiDivisorZeroIndex,
    (finiteLaplace f d (s - riemannXiDivisorZeroValue p) + f 0 / riemannXiDivisorZeroValue p)

/-- The negative-even-zero sum paired with its reciprocal constants. -/
def smoothedGammaPairedSum (f : ℝ → ℂ) (d : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (finiteLaplace f d (s - shiftedGammaPole n) + f 0 / shiftedGammaPole n)

private theorem xi_bounded_finite (R : ℝ) :
    {p : RiemannXiDivisorZeroIndex | ‖riemannXiDivisorZeroValue p‖ ≤ R}.Finite :=
  Hadamard.divisorZeroIndex₀_norm_le_finite (f := riemannXi) (U := univ) (B := R) (by simp)

private theorem gamma_bounded_finite (R : ℝ) : {n : ℕ | ‖shiftedGammaPole n‖ ≤ R}.Finite := by
  apply (Set.finite_Iic ⌈R⌉₊).subset
  intro n hn
  have heq : ‖shiftedGammaPole n‖ = 2 * ((n : ℝ) + 1) := by
    simp [shiftedGammaPole, norm_natCast_add_one]
  have hle : (n : ℝ) ≤ R := by
    have := Nat.cast_nonneg (α := ℝ) n
    change ‖shiftedGammaPole n‖ ≤ R at hn
    rw [heq] at hn
    linarith
  exact_mod_cast hle.trans (Nat.le_ceil R)

private theorem summable_gamma_inv_sq : Summable (fun n : ℕ => ‖shiftedGammaPole n‖⁻¹ ^ 2) := by
  have hp := (summable_nat_add_iff 1).mpr
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ)))
  have hp' : Summable (fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, inv_pow] using hp
  apply (hp'.mul_left ((2 : ℝ)⁻¹ ^ 2)).congr
  intro n
  simp [shiftedGammaPole, norm_natCast_add_one, mul_pow, mul_comm]

variable {f g h : ℝ → ℂ} {d M : ℝ}
  (hd : 0 ≤ d) (hM : 0 ≤ M)
  (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
  (hh : ContinuousOn h (Icc 0 d))
  (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t)
  (hgh : ∀ t ∈ Ioo 0 d, HasDerivAt g (h t) t)
  (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
  (hbound : ∀ t ∈ Icc 0 d, ‖h t‖ ≤ M)

include hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound

/-- The complex xi paired series converges absolutely at every parameter. -/
theorem summable_smoothedXiPaired (s : ℂ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      finiteLaplace f d (s - riemannXiDivisorZeroValue p) + f 0 / riemannXiDivisorZeroValue p) :=
  summable_finiteLaplace_add_reciprocal riemannXiDivisorZeroValue xi_bounded_finite
    summable_riemannXiDivisorZero_norm_inv_sq
    (fun p => (riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)).2)
    hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound s

/-- The complex xi paired sum is entire, by a locally uniform summable majorant. -/
theorem differentiable_smoothedXiPairedSum : Differentiable ℂ (smoothedXiPairedSum f d) :=
  differentiable_tsum_finiteLaplace_add_reciprocal riemannXiDivisorZeroValue xi_bounded_finite
    summable_riemannXiDivisorZero_norm_inv_sq
    (fun p => (riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)).2)
    hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound

/-- The complex gamma paired series converges absolutely at every parameter. -/
theorem summable_smoothedGammaPaired (s : ℂ) :
    Summable (fun n : ℕ => finiteLaplace f d (s - shiftedGammaPole n) + f 0 / shiftedGammaPole n) :=
  summable_finiteLaplace_add_reciprocal shiftedGammaPole gamma_bounded_finite
    summable_gamma_inv_sq shiftedGammaPole_re_nonpos
    hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound s

/-- The paired negative-even-zero sum is entire, including at its original poles. -/
theorem differentiable_smoothedGammaPairedSum : Differentiable ℂ (smoothedGammaPairedSum f d) :=
  differentiable_tsum_finiteLaplace_add_reciprocal shiftedGammaPole gamma_bounded_finite
    summable_gamma_inv_sq shiftedGammaPole_re_nonpos
    hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound

end

end PrimeFactorUnimodality
