import PrimeFactorUnimodality.Helpers.Analytic.KadiriInitialMaster

/-! # Initial numerical zero-free region and finite-harmonic separation

Test both signs of height, the exact high cutoff, the symmetric strip, and
every natural harmonic in arbitrary finite degree. Low-height information
remains an explicit premise; no RH or final numerical region is asserted.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Real

example {ρ : ℂ} (hρ : riemannXi ρ = 0) (ht : 10 ^ 9 ≤ |ρ.im|) :
    1 / (56 * Real.log |ρ.im|) ≤ 1 - ρ.re := xi_zero_gap_initial hρ ht

example {ρ : ℂ} (hρ : riemannXi ρ = 0) (ht : 10 ^ 9 ≤ ρ.im) :
    1 / (56 * Real.log ρ.im) ≤ 1 - ρ.re := by
  have hp : 0 ≤ ρ.im := by linarith
  simpa only [abs_of_nonneg hp] using
    xi_zero_gap_initial hρ (by rwa [abs_of_nonneg hp])

example {ρ : ℂ} (hρ : riemannXi ρ = 0) (ht : ρ.im ≤ -(10 ^ 9)) :
    1 / (56 * Real.log (-ρ.im)) ≤ 1 - ρ.re := by
  have hn : ρ.im ≤ 0 := by linarith
  simpa only [abs_of_nonpos hn] using
    xi_zero_gap_initial hρ (by rw [abs_of_nonpos hn]; linarith)

example {s : ℂ} (ht : |s.im| = 10 ^ 9)
    (hs : 1 - 1 / (56 * Real.log (10 ^ 9)) < s.re) : riemannXi s ≠ 0 := by
  apply riemannXi_ne_zero_initial (by rw [ht])
  simpa only [ht] using hs

example {A σ : ℝ}
    (hupper : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < A → (riemannXiDivisorZeroValue p).re ≤ σ)
    {p : RiemannXiDivisorZeroIndex} (hp : |(riemannXiDivisorZeroValue p).im| < A) :
    1 - σ ≤ (riemannXiDivisorZeroValue p).re ∧ (riemannXiDivisorZeroValue p).re ≤ σ :=
  kadiriCentralStrip_of_upper_below hupper hp

example {A σ t H : ℝ} (hσ : 1 - 1 / (56 * Real.log A) ≤ σ)
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < 10 ^ 9 → (riemannXiDivisorZeroValue p).re ≤ σ)
    (n : ℕ) (hA : (n : ℝ) * |t| + H ≤ A) :
    ∀ i ∈ Finset.range (n + 1), ∀ p : RiemannXiDivisorZeroIndex,
      ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue p) →
        |(i : ℝ) * t| + H ≤ |(riemannXiDivisorZeroValue p).im| := by
  apply kadiri_outer_separation_initial_harmonics (t := t) (H := H) hσ hlow
    (Finset.range (n + 1)) (fun i : ℕ => (i : ℝ))
  intro i hi
  have hin : i ≤ n := by simpa using Finset.mem_range.mp hi
  have hir : (i : ℝ) ≤ n := by exact_mod_cast hin
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg i)]
  have h := mul_le_mul_of_nonneg_right hir (abs_nonneg t)
  linarith only [h, hA]

example {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < 10 ^ 9 → (riemannXiDivisorZeroValue p).re = 1 / 2) :
    ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < 10 ^ 9 → (riemannXiDivisorZeroValue p).re ≤ σ := by
  intro p hp
  rw [hlow p hp]
  exact hσ

end

end PrimeFactorUnimodality.Tests
