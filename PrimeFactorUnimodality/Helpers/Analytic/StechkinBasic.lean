import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiZeros
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson.Stechkin
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.ZetaTrigonometricShift

set_option autoImplicit false

/-! # Stechkin kernels and compactly smoothed prime sums

The paired-zero inequality applies to actual xi zeros, including the full
retained pole at the zero's height. Compact smoothing makes the shifted
von Mangoldt positivity argument valid even inside the critical strip.
These are pointwise ingredients: pairing the entire divisor sum and the
smoothed explicit formula require separate arguments.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex
open scoped BigOperators ComplexConjugate

/-- The real kernel contributed by a zero and its reflection across the critical line. -/
def stechkinZeroPair (s ρ : ℂ) : ℝ :=
  (1 / (s - ρ) + 1 / (s - 1 + conj ρ)).re

/-- The complex reflected-zero kernel is the real-variable paired Poisson kernel. -/
theorem stechkinZeroPair_eq (σ t : ℝ) (ρ : ℂ) :
    stechkinZeroPair ((σ : ℂ) + t * I) ρ = Real.stechkinPair σ ρ.re (t - ρ.im) := by
  simp [stechkinZeroPair, Real.stechkinPair, one_div, inv_re, normSq_apply,
    pow_two, sub_eq_add_neg]

/-- Every xi zero contributes a nonnegative Stechkin pair difference. -/
theorem stechkinZeroPair_sub_nonneg {σ : ℝ} (hσ : 1 < σ)
    {ρ : ℂ} (hρ : riemannXi ρ = 0) (t : ℝ) :
    0 ≤ stechkinZeroPair ((σ : ℂ) + t * I) ρ -
      (1 / Real.sqrt 5) * stechkinZeroPair ((Real.stechkinShift σ : ℂ) + t * I) ρ := by
  obtain ⟨hτ, hrel⟩ := Real.stechkinShift_spec hσ
  obtain ⟨hβ₀, hβ₁⟩ := riemannXi_zero_mem_critical_strip hρ
  rw [stechkinZeroPair_eq, stechkinZeroPair_eq]
  exact sub_nonneg.mpr (Real.stechkinPair_le hσ hτ hrel hβ₀ hβ₁ _)

/-- At a zero's height the shifted pair still retains the entire pole term. -/
theorem stechkinZeroPair_aligned_le {σ : ℝ} (hσ : 1 < σ)
    {ρ : ℂ} (hρ : riemannXi ρ = 0) :
    1 / (σ - ρ.re) ≤ stechkinZeroPair ((σ : ℂ) + ρ.im * I) ρ -
      (1 / Real.sqrt 5) *
        stechkinZeroPair ((Real.stechkinShift σ : ℂ) + ρ.im * I) ρ := by
  obtain ⟨hτ, hrel⟩ := Real.stechkinShift_spec hσ
  obtain ⟨hβ₀, hβ₁⟩ := riemannXi_zero_mem_critical_strip hρ
  rw [stechkinZeroPair_eq, stechkinZeroPair_eq, sub_self]
  exact le_sub_iff_add_le.mpr (Real.stechkinPair_aligned_le hσ hτ hrel hβ₀ hβ₁)

/-- The von Mangoldt Dirichlet series smoothed by a function of the logarithm. -/
def smoothedVonMangoldt (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (f (Real.log n) : ℂ) *
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n

/-- Compact smoothing discharges convergence on every vertical line. -/
theorem summable_smoothedVonMangoldt {f : ℝ → ℝ} {d : ℝ}
    (hf : ∀ x, d < x → f x = 0) (s : ℂ) :
    Summable (fun n : ℕ => (f (Real.log n) : ℂ) *
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n) :=
  summable_weighted_vonMangoldt_of_hasFiniteSupport (hasFiniteSupport_log_weight hf) s

/-- Smoothed positivity has no restriction that the original real part exceed one. -/
theorem sum_mul_re_shifted_smoothedVonMangoldt_nonneg {ι : Type*}
    (s : Finset ι) (a k : ι → ℝ) {f : ℝ → ℝ} {d σ τ κ : ℝ}
    (hf : ∀ x, d < x → f x = 0) (hf₀ : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hστ : σ ≤ τ) (hκ : κ ≤ 1) (t : ℝ)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ s, a i * Real.cos (k i * u)) :
    0 ≤ ∑ i ∈ s, a i *
      ((smoothedVonMangoldt f ((σ : ℂ) + (k i * t : ℝ) * I)).re -
        κ * (smoothedVonMangoldt f ((τ : ℂ) + (k i * t : ℝ) * I)).re) :=
  sum_mul_re_shifted_weighted_vonMangoldt_nonneg s a k (fun n => f (Real.log n))
    (fun n => hf₀ _ (Real.log_natCast_nonneg n)) hστ hκ t
    (fun _ => summable_smoothedVonMangoldt hf _)
    (fun _ => summable_smoothedVonMangoldt hf _) hpoly

end

end PrimeFactorUnimodality
