import PrimeFactorUnimodality.Helpers.Analytic.KadiriUniformBootstrap
import PrimeFactorUnimodality.Helpers.Analytic.MossinghoffTrudgianPolynomial

/-! # Exact polynomial construction and uniform-parameter regressions

Include empty and singleton supports, signed generating coefficients,
frequencies beyond the support, zero affine offset, equal endpoint heights,
and the actual normalized polynomial's global phase bound.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Finset Real

example (c : ℕ → ℝ) (k : ℕ) : cosineAutocorrelationCoeff ∅ c k = 0 := by
  simp [cosineAutocorrelationCoeff]

example (c : ℕ → ℝ) (j : ℕ) : cosineAutocorrelationCoeff {j} c 0 = c j ^ 2 := by
  simp

example (c : ℕ → ℝ) : cosineAutocorrelationCoeff (range 0) c 0 = 0 := by
  simp

example (c : ℕ → ℝ) {n k : ℕ} (hk : 0 < k) (hnk : n ≤ k) :
    cosineAutocorrelationCoeff (range n) c k = 0 := by
  rw [cosineAutocorrelationCoeff_range_pos n c hk, Nat.sub_eq_zero_of_le hnk]
  simp

example (c : ℕ → ℝ) : cosineAutocorrelationCoeff (range 2) c 1 = 2 * c 0 * c 1 := by
  rw [cosineAutocorrelationCoeff_range_pos 2 c (by decide)]
  norm_num [Finset.sum_range_succ]
  ring

example (u : ℝ) :
    0 ≤ ∑ k ∈ range 2,
      cosineAutocorrelationCoeff (range 2) (fun i => if i = 0 then 1 else -1) k *
        cos ((k : ℝ) * u) :=
  sum_cosineAutocorrelationCoeff_mul_cos_nonneg _ _ 1
    (by intro i hi; simp only [mem_range] at hi; omega) u

example : cosineAutocorrelationCoeff (range 2) (fun i => if i = 0 then 1 else -1) 1 = -2 := by
  rw [cosineAutocorrelationCoeff_range_pos 2 _ (by decide)]
  norm_num [Finset.sum_range_succ]

example (c : ℕ → ℝ) (n : ℕ) (u : ℝ) :
    0 ≤ ∑ k ∈ range (n + 1), cosineAutocorrelationCoeff (range (n + 1)) c k *
      cos ((k : ℝ) * u) :=
  sum_cosineAutocorrelationCoeff_mul_cos_nonneg _ _ n
    (by intro i hi; exact Nat.le_of_lt_succ (mem_range.mp hi)) u

example : mossinghoffTrudgianCoefficient 0 = 1 := mossinghoffTrudgianCoefficient_zero

example (u : ℝ) :
    0 ≤ ∑ k ∈ range 17, mossinghoffTrudgianCoefficient k * cos ((k : ℝ) * u) :=
  mossinghoffTrudgianPolynomial_nonneg u

example {a b T : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) (hT : 1 < T) :
    log T / log (a * T + b) ≤ log T / log (a * T + b) :=
  log_div_log_affine_le ha hb hT le_rfl

example {a T t : ℝ} (ha : 1 ≤ a) (hT : 1 < T) (hTt : T ≤ t) :
    log T / log (a * T) ≤ log t / log (a * t) := by
  simpa using log_div_log_affine_le ha (show (0 : ℝ) ≤ 0 from le_rfl) hT hTt

example {t : ℝ} (ht : 1 < t) : log t / log (1 * t + 0) = 1 := by
  simp [ne_of_gt (log_pos ht)]

example {n : ℕ} {t H : ℝ} (ht : 0 ≤ t) : |(n : ℝ) * t| + H ≤ (n : ℝ) * t + H :=
  kadiri_harmonics_le_cutoff (by simp) ht

example {R H T t : ℝ} {n : ℕ} (hR : 0 < R) (hn : 1 ≤ n) (hH : 0 ≤ H)
    (hT : 1 < T) (hTt : T ≤ t) : kadiriBootstrapSigma R n H T ≤ kadiriBootstrapSigma R n H t :=
  kadiriBootstrapSigma_le hR hn hH hT hTt

example {r T t η : ℝ} (hr : 0 < r) (hT : 1 < T) (hTt : T ≤ t)
    (hsmall : η ≤ 1 / (r * log t)) : η ≤ 1 / (r * log T) :=
  kadiriBootstrapScale_le_endpoint hr hT hTt hsmall

example {R r H T t η : ℝ} {n : ℕ} (hR : 0 < R) (hr : 0 < r) (hn : 1 ≤ n)
    (hH : 0 ≤ H) (hT : 1 < T) (hTt : T ≤ t) (hη : 0 < η)
    (hprior : 1 / (R * log t) ≤ η) (hsmall : η ≤ 1 / (r * log t)) :
    (1 - kadiriBootstrapSigma R n H t) / η ∈
      Set.Icc (kadiriBootstrapLowerArgument R r n H T) 1 :=
  kadiriBootstrapArgument_mem_Icc hR hr hn hH hT hTt hη hprior hsmall

example {R t η η₁ : ℝ} (hR : 0 < R) (ht : 1 < t) (hη₁ : 0 < η₁)
    (hprior : 1 / (R * log t) ≤ η) (hsmall : η ≤ η₁) : exp (1 / (R * η₁)) ≤ t :=
  kadiriBootstrapHeightLower_of_small_scale hR ht hη₁ hprior hsmall

example {θ η η₀ σ₀ κ δ M P L₀ L₁ G q : ℝ} {S : Finset ℕ} {a : ℕ → ℝ}
    (hη : 0 ≤ η) (hη₀ : 0 < η₀) (hηη₀ : η ≤ η₀)
    (h₂ : 0 ≤ kadiriCorrectionQuadratic θ σ₀ κ M P L₀ L₁ q)
    (h₃ : 0 ≤ kadiriCorrectionCubic θ η₀ σ₀ κ δ L₀ S a) :
    kadiriCorrectionPolynomial θ η η₀ σ₀ κ δ M P L₀ L₁ G q S a ≤
      (η / η₀) * kadiriCorrectionPolynomial θ η₀ η₀ σ₀ κ δ M P L₀ L₁ G q S a :=
  kadiriCorrectionPolynomial_le_scaled_endpoint hη hη₀ hηη₀ h₂ h₃

example {θ η η₁ η₀ σ₀ κ δ M P L₀ L₁ G q : ℝ} {S : Finset ℕ} {a : ℕ → ℝ}
    (hη : 0 ≤ η) (hη₀ : 0 < η₀) (hηη₀ : η ≤ η₀) (hη₁η : η₁ ≤ η)
    (h₂ : 0 ≤ kadiriCorrectionQuadratic θ σ₀ κ M P L₀ L₁ q)
    (h₃ : 0 ≤ kadiriCorrectionCubic θ η₀ σ₀ κ δ L₀ S a)
    (hend : kadiriCorrectionPolynomial θ η₀ η₀ σ₀ κ δ M P L₀ L₁ G q S a ≤ 0) :
    kadiriCorrectionPolynomial θ η η₀ σ₀ κ δ M P L₀ L₁ G q S a ≤
      (η₁ / η₀) * kadiriCorrectionPolynomial θ η₀ η₀ σ₀ κ δ M P L₀ L₁ G q S a :=
  kadiriCorrectionPolynomial_le_band_endpoint hη hη₀ hηη₀ hη₁η h₂ h₃ hend

end

end PrimeFactorUnimodality.Tests
