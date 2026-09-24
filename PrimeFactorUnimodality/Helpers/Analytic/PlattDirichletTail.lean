import PrimeFactorUnimodality.Helpers.Analytic.PlattDirichletTerms
import PrimeFactorUnimodality.Mathlib.Analysis.PSeries.TailBound

set_option autoImplicit false

/-! # Convergence and truncation of the actual Gamma Dirichlet series

Contour decay controls every omitted term. The integral test gives a
closed tail budget after any positive cutoff, and the exact infinite-sum
decomposition identifies that tail with the finite-prefix error.
The separate equality with the zeta-window transform is not assumed here.
-/

open Finset

namespace PrimeFactorUnimodality

noncomputable section

/-- The entire positive-index Gamma Dirichlet series. -/
def plattDirichletSeries (k : ℕ) (t₀ h x : ℝ) : ℂ :=
  ∑' n : ℕ, plattDirichletTerm k t₀ h x (n + 1)

/-- The integral-test budget after the first `J` terms. -/
def plattDirichletTailBound (m k : ℕ) (t₀ h x : ℝ) (J : ℕ) : ℝ :=
  plattDirichletMajorant m k t₀ h x * ((J : ℝ) ^ (-(2 * (m : ℝ))) / (2 * (m : ℝ)))

/-- The actual shifted terms converge, including when the prefix is empty. -/
theorem summable_plattDirichletTail (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) (J : ℕ) :
    Summable (fun n : ℕ => plattDirichletTerm k t₀ h x (n + J + 1)) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact summable_of_norm_le_rpow_tail (p := 2 * (m : ℝ) + 1) (by linarith)
    (fun n => norm_plattDirichletTerm_le m k hm ht₀ hh x (by omega))

/-- Contour decay bounds the entire omitted infinite sum, at every real frequency. -/
theorem norm_plattDirichletTail_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) {J : ℕ} (hJ : 0 < J) :
    ‖∑' n : ℕ, plattDirichletTerm k t₀ h x (n + J + 1)‖ ≤
      plattDirichletTailBound m k t₀ h x J := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ht := norm_tsum_le_rpow_tail (p := 2 * (m : ℝ) + 1)
    (plattDirichletMajorant_nonneg m k hm ht₀ hh x) (by linarith) hJ
    (fun n => norm_plattDirichletTerm_le m k hm ht₀ hh x (by omega))
  simpa only [plattDirichletTailBound, show 1 - (2 * (m : ℝ) + 1) = -(2 * (m : ℝ)) by ring,
    add_sub_cancel_right] using ht

/-- The finite-prefix error is exactly the true tail, not a separately postulated remainder. -/
theorem plattDirichletSeries_sub_prefix_eq (k : ℕ)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) (J : ℕ) :
    plattDirichletSeries k t₀ h x - ∑ n ∈ range J, plattDirichletTerm k t₀ h x (n + 1) =
      ∑' n : ℕ, plattDirichletTerm k t₀ h x (n + J + 1) := by
  have hs := summable_plattDirichletTail 1 k (by omega) ht₀ hh x 0
  simpa only [Nat.add_zero, plattDirichletSeries] using
    (eq_sub_of_add_eq' (hs.sum_add_tsum_nat_add J)).symm

/-- Full Dirichlet truncation, retaining the exact cutoff power and all contour factors. -/
theorem norm_plattDirichletSeries_sub_prefix_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) {J : ℕ} (hJ : 0 < J) :
    ‖plattDirichletSeries k t₀ h x -
        ∑ n ∈ range J, plattDirichletTerm k t₀ h x (n + 1)‖ ≤
      plattDirichletTailBound m k t₀ h x J := by
  rw [plattDirichletSeries_sub_prefix_eq k ht₀ hh x J]
  exact norm_plattDirichletTail_le m k hm ht₀ hh x hJ

end

end PrimeFactorUnimodality
