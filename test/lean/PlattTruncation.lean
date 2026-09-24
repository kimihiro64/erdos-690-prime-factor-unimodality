import PrimeFactorUnimodality.Helpers.Analytic.PlattDirichletTail
import PrimeFactorUnimodality.Helpers.Analytic.PlattTaylorAssembly

/-! The actual transforms and actual infinite series satisfy every truncation bound. -/

open Finset PrimeFactorUnimodality
open scoped FourierTransform Nat

example (k : ℕ) (t₀ u w : ℝ) {h : ℝ} (hh : 0 < h) :
    ‖𝓕 (plattWindowKernel k t₀ h) (u + w) - plattFourierTaylor 4 k t₀ h u w‖ ≤
      plattWindowL1Bound (k + 4) h * |w| ^ 4 / 24 := by
  simpa only [plattFourierTaylorBound, show (4 ! : ℝ) = 24 by norm_num] using
    norm_fourier_plattWindowKernel_sub_taylor_le 4 k t₀ u w hh

example (k : ℕ) (t₀ u w : ℝ) {h : ℝ} (hh : 0 < h) :
    ‖𝓕 (plattWindowKernel k t₀ h) (u + w) - plattFourierTaylor 0 k t₀ h u w‖ ≤
      plattWindowL1Bound k h := by
  simpa [plattFourierTaylorBound] using
    norm_fourier_plattWindowKernel_sub_taylor_le 0 k t₀ u w hh

example (K k : ℕ) (u : ℝ) {h w ξ : ℝ} (hh : 0 < h) (hw : |w| ≤ ξ) :
    ‖𝓕 (plattWindowKernel k (-1000) h) (u + w) -
        plattFourierTaylor K k (-1000) h u w‖ ≤ plattFourierTaylorBound K k h ξ :=
  norm_fourier_plattWindowKernel_sub_taylor_le_radius K k (-1000) u hh hw

example (K k : ℕ) (t₀ u w : ℝ) {h : ℝ} (hh : 0 < h) {q : ℕ → ℂ} {ε : ℕ → ℝ}
    (hq : ∀ r ∈ range K, ‖𝓕 (plattWindowKernel (k + r) t₀ h) u - q r‖ ≤ ε r) :
    ‖𝓕 (plattWindowKernel k t₀ h) (u + w) -
        ∑ r ∈ range K, (w ^ r / (r ! : ℝ)) • q r‖ ≤
      plattFourierTaylorBound K k h |w| + ∑ r ∈ range K, (|w| ^ r / (r ! : ℝ)) * ε r :=
  norm_fourier_plattWindowKernel_sub_approx_taylor_le K k t₀ u w hh hq

example {ι : Type*} (s : Finset ι) (c : ι → ℂ) (u w : ι → ℝ)
    (K k : ℕ) (t₀ : ℝ) {h ξ : ℝ} (hh : 0 < h) (hw : ∀ j ∈ s, |w j| ≤ ξ) :
    ‖(∑ j ∈ s, c j * 𝓕 (plattWindowKernel k t₀ h) (u j + w j)) -
        ∑ j ∈ s, c j * plattFourierTaylor K k t₀ h (u j) (w j)‖ ≤
      (∑ j ∈ s, ‖c j‖) * plattFourierTaylorBound K k h ξ :=
  norm_sum_fourier_plattWindowKernel_sub_taylor_le s c u w K k t₀ hh hw

example (t₀ : ℝ) : ‖plattDirichletWeight t₀ 4‖ = 1 / 2 := by
  have hs : Real.sqrt 4 = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  simpa only [Nat.cast_ofNat, hs] using
    norm_plattDirichletWeight_eq_inv_sqrt t₀ (by norm_num : 0 < (4 : ℕ))

example (k : ℕ) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) {j : ℕ}
    (hj : 0 < j) : ‖plattDirichletTerm k t₀ h x j‖ ≤
      plattDirichletMajorant 1 k t₀ h x * (j : ℝ) ^ (-(3 : ℝ)) := by
  convert norm_plattDirichletTerm_le 1 k (by omega) ht₀ hh x hj using 1
  norm_num

example (k : ℕ) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) :
    Summable (fun n : ℕ => plattDirichletTerm k t₀ h x (n + 1)) := by
  simpa only [Nat.add_zero] using summable_plattDirichletTail 1 k (by omega) ht₀ hh x 0

example (m k : ℕ) (hm : 1 ≤ m) {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h)
    (x : ℝ) {J : ℕ} (hJ : 0 < J) :
    ‖plattDirichletSeries k t₀ h x - ∑ n ∈ range J, plattDirichletTerm k t₀ h x (n + 1)‖ ≤
      plattDirichletMajorant m k t₀ h x * ((J : ℝ) ^ (-(2 * (m : ℝ))) / (2 * (m : ℝ))) :=
  norm_plattDirichletSeries_sub_prefix_le m k hm ht₀ hh x hJ
