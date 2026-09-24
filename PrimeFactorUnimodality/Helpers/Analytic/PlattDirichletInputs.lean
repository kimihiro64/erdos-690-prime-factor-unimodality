import PrimeFactorUnimodality.Helpers.Analytic.PlattDirichletTerms
import PrimeFactorUnimodality.Helpers.Analytic.PlattTaylorInputs

set_option autoImplicit false

/-! # Finite Dirichlet evaluation with enclosed weights, shifts and columns

Every weight error multiplies a proved uniform transform bound. Every
transform error multiplies the norm of the approximate weight. Thus neither
phase uncertainty nor logarithmic-shift uncertainty disappears in assembly.
-/

open Finset
open scoped FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- The complete absolute error of one computed Dirichlet term. -/
def plattDirichletInputError (K k : ℕ) (h w σ η : ℝ) (c : ℂ) (ε : ℕ → ℝ) : ℝ :=
  η * plattWindowL1Bound k h + ‖c‖ * plattTaylorInputError K k h w σ ε

/-- The genuine weighted term is enclosed, including approximate weight and shift data. -/
theorem norm_plattDirichletTerm_sub_approx_le (K k j : ℕ) (t₀ x u w : ℝ)
    {h σ η : ℝ} (hh : 0 < h) {c : ℂ}
    (hc : ‖plattDirichletWeight t₀ j - c‖ ≤ η)
    (hs : |x + plattDirichletShift j - (u + w)| ≤ σ)
    {q : ℕ → ℂ} {ε : ℕ → ℝ}
    (hq : ∀ r ∈ range K, ‖𝓕 (plattWindowKernel (k + r) t₀ h) u - q r‖ ≤ ε r) :
    ‖plattDirichletTerm k t₀ h x j - c * plattApproxTaylor K q w‖ ≤
      plattDirichletInputError K k h w σ η c ε := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hc
  have hw : ‖plattDirichletTerm k t₀ h x j -
      c * 𝓕 (plattWindowKernel k t₀ h) (x + plattDirichletShift j)‖ ≤
      η * plattWindowL1Bound k h := by
    rw [plattDirichletTerm, ← sub_mul, norm_mul]
    exact mul_le_mul hc (norm_fourier_plattWindowKernel_le k t₀ _ hh) (norm_nonneg _) hη
  have ht : ‖c * 𝓕 (plattWindowKernel k t₀ h) (x + plattDirichletShift j) -
      c * plattApproxTaylor K q w‖ ≤ ‖c‖ * plattTaylorInputError K k h w σ ε := by
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_fourier_plattWindowKernel_sub_approx_input_le K k t₀ u w _ hh hs hq) (norm_nonneg c)
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (c * 𝓕 (plattWindowKernel k t₀ h) (x + plattDirichletShift j)) _).trans (add_le_add hw ht)

/-- The finite prefix represented by the approximate weights and Taylor columns. -/
def plattApproxDirichletPrefix (J K : ℕ) (c : ℕ → ℂ) (q : ℕ → ℕ → ℂ) (w : ℕ → ℝ) : ℂ :=
  ∑ n ∈ range J, c n * plattApproxTaylor K (q n) (w n)

/-- Summing term errors preserves every positive-index contribution. -/
theorem norm_plattDirichletPrefix_sub_approx_le (J K k : ℕ) (t₀ x : ℝ)
    {h : ℝ} (hh : 0 < h) {c : ℕ → ℂ} {u w σ η : ℕ → ℝ}
    (hc : ∀ n ∈ range J, ‖plattDirichletWeight t₀ (n + 1) - c n‖ ≤ η n)
    (hs : ∀ n ∈ range J, |x + plattDirichletShift (n + 1) - (u n + w n)| ≤ σ n)
    {q : ℕ → ℕ → ℂ} {ε : ℕ → ℕ → ℝ}
    (hq : ∀ n ∈ range J, ∀ r ∈ range K,
      ‖𝓕 (plattWindowKernel (k + r) t₀ h) (u n) - q n r‖ ≤ ε n r) :
    ‖(∑ n ∈ range J, plattDirichletTerm k t₀ h x (n + 1)) -
        plattApproxDirichletPrefix J K c q w‖ ≤
      ∑ n ∈ range J, plattDirichletInputError K k h (w n) (σ n) (η n) (c n) (ε n) := by
  rw [plattApproxDirichletPrefix, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  exact sum_le_sum fun n hn =>
    norm_plattDirichletTerm_sub_approx_le K k (n + 1) t₀ x (u n) (w n) hh
      (hc n hn) (hs n hn) (hq n hn)

end

end PrimeFactorUnimodality
