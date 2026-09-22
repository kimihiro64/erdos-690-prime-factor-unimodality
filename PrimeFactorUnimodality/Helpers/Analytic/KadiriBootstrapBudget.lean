import PrimeFactorUnimodality.Helpers.Analytic.KadiriExplicitMaster
import PrimeFactorUnimodality.Helpers.Analytic.KadiriTransformGap

/-! # The complete error budget after retaining the transform gap

Extract the unique zero harmonic from a finite set of natural frequencies.
Its exact pole transform combines with the distinguished-zero transform
to give the paper's `K(w,theta)`. Every remaining pole, zero-tail, Gamma,
and retained-pair contribution is kept in the explicit budget.
There is no restriction on the degree or a numerical positivity assumption.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The inverse-height-square sum of all nonzero harmonics. -/
def kadiriPoleCoefficient (S : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ S.erase 0, a i / ((i : ℝ) * t) ^ 2

/-- The remaining explicit upper budget, including the zero-tail subtraction. -/
def kadiriBootstrapBudget (θ η η₀ σ₀ σ κ δ z H t : ℝ)
    (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  kadiriPoleError θ η z * kadiriPoleCoefficient S a t +
    a 1 * kadiriRetainedPairError θ η η₀ σ₀ κ δ +
    kadiriOuterError θ η κ σ₀ z / 2 *
      (∑ i ∈ S, a i * xiLehmanTailMajorant ((i : ℝ) * t) H) +
    kadiriWeight θ η 0 *
      (∑ i ∈ S, a i * smoothedGammaFactorMajorant κ σ ((i : ℝ) * t)) +
    (∑ i ∈ S, a i) * ((1 + κ) * η ^ 3 * (-kadiriKernel₂ θ 0) / 4)

/-- Split exactly one zero harmonic, leaving a factorized inverse-height-square sum. -/
theorem sum_kadiriPoleMajorant_nat_eq {θ η z σ t : ℝ} (ht : t ≠ 0)
    (S : Finset ℕ) (h₀ : 0 ∈ S) (a : ℕ → ℝ) :
    (∑ i ∈ S, a i * kadiriPoleMajorant θ η z σ ((i : ℝ) * t)) =
      a 0 * (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
        (kadiriWeightSupport θ η) ((σ - 1 : ℝ) : ℂ)).re +
      kadiriPoleError θ η z * kadiriPoleCoefficient S a t := by
  rw [← Finset.add_sum_erase S _ h₀]
  simp only [Nat.cast_zero, zero_mul, kadiriPoleMajorant, ↓reduceIte]
  congr 1
  rw [kadiriPoleCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≠ 0 := (Finset.mem_erase.mp hi).1
  have hiR : (i : ℝ) ≠ 0 := by exact_mod_cast hin
  simp only [mul_ne_zero hiR ht, ↓reduceIte]
  ring

/-- The actual normalized transform gap is bounded by the complete remaining budget. -/
theorem kadiriTransformGap_le_budget_of_master {θ η η₀ σ₀ σ κ δ z H t β : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hηβ : η = 1 - β) (ht : t ≠ 0)
    (S : Finset ℕ) (h₀ : 0 ∈ S) (a : ℕ → ℝ)
    (hm : 0 ≤ (∑ i ∈ S, a i * kadiriPoleMajorant θ η z σ ((i : ℝ) * t)) -
      a 1 * ((finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
        (kadiriWeightSupport θ η) ((σ - β : ℝ) : ℂ)).re -
          kadiriRetainedPairError θ η η₀ σ₀ κ δ) +
      kadiriOuterError θ η κ σ₀ z / 2 *
        (∑ i ∈ S, a i * xiLehmanTailMajorant ((i : ℝ) * t) H) +
      kadiriWeight θ η 0 *
        (∑ i ∈ S, a i * smoothedGammaFactorMajorant κ σ ((i : ℝ) * t)) +
      (∑ i ∈ S, a i) * ((1 + κ) * η ^ 3 * (-kadiriKernel₂ θ 0) / 4)) :
    kadiriTransformGap θ (a 0) (a 1) ((1 - σ) / η) ≤
      kadiriBootstrapBudget θ η η₀ σ₀ σ κ δ z H t S a := by
  rw [sum_kadiriPoleMajorant_nat_eq ht S h₀ a] at hm
  rw [← kadiriWeight_transform_gap_eq hθ hη hηβ]
  unfold kadiriBootstrapBudget
  linarith only [hm]

end

end PrimeFactorUnimodality
