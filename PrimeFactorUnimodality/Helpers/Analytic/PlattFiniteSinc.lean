import PrimeFactorUnimodality.Helpers.Analytic.PlattSincInterpolation
import PrimeFactorUnimodality.Helpers.Analytic.PlattSincTail
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.SymmetricTruncation

set_option autoImplicit false

/-! # Finite sinc interpolation with analytic tails and approximate sample errors

Exactly `2*M+1` samples are retained. The first omitted radius is `(M+1)/A`,
not `M/A`. Spectral error, both omitted time tails, all retained sample
uncertainties and final arithmetic error remain explicit.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- A finite interpolation sum using a supplied sequence of sample values. -/
def plattFiniteSinc (M : ℕ) (A v : ℝ) (q : ℤ → ℂ) : ℂ :=
  Fourier.symmetricSum (fun n => q n * (Real.sinc (Real.pi * (A * v - n)) : ℂ)) M

/-- The norm of an individual sinc term never exceeds the norm of its sample. -/
theorem norm_plattSincTerm_le (z : ℂ) (x : ℝ) :
    ‖z * (Real.sinc x : ℂ)‖ ≤ ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one x) (norm_nonneg z)).trans_eq (mul_one _)

/-- Finite truncation retains both exactly summed Gaussian-majorant tails. -/
theorem norm_plattZetaSinc_sub_finite_le (M k : ℕ) (t₀ v : ℝ) {h A : ℝ}
    (hh : 0 < h) (hA : 0 < A)
    (hk : ((k : ℝ) + 1) * h ^ 2 < (((M : ℝ) + 1) / A) ^ 2) :
    ‖(∑' n : ℤ, plattZetaWindow k t₀ h ((n : ℝ) / A) *
        (Real.sinc (Real.pi * (A * v - n)) : ℂ)) -
      plattFiniteSinc M A v (fun n => plattZetaWindow k t₀ h ((n : ℝ) / A))‖ ≤
      plattSincTailError k t₀ h A (((M : ℝ) + 1) / A) := by
  have hR : 0 < ((M : ℝ) + 1) / A := by positivity
  apply Fourier.norm_tsum_sub_symmetricSum_le
    (summable_plattZetaWindow_sinc k t₀ v hh hA) M
    (hasSum_plattSincTailMajorant k t₀ hh hA hR hk)
  · intro n
    apply (norm_plattSincTerm_le _ _).trans
    apply norm_plattZetaWindow_le_sincTailMajorant k t₀ hh hA hR n
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [abs_div, abs_of_pos hA, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + M + 1)]
    ring
  · intro n
    apply (norm_plattSincTerm_le _ _).trans
    apply norm_plattZetaWindow_le_sincTailMajorant k t₀ hh hA hR n
    simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_div, abs_neg]
    rw [abs_div, abs_of_pos hA, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + M + 1)]
    ring

/-- Spectral and time truncation give a bound for the finite sum of genuine samples. -/
theorem norm_plattZetaWindow_sub_finiteSinc_le (m M k : ℕ) (hm : 1 ≤ m)
    {t₀ h A : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A)
    (hk : ((k : ℝ) + 1) * h ^ 2 < (((M : ℝ) + 1) / A) ^ 2) (v : ℝ) :
    ‖plattZetaWindow k t₀ h v -
      plattFiniteSinc M A v (fun n => plattZetaWindow k t₀ h ((n : ℝ) / A))‖ ≤
      plattSincError m k t₀ h A + plattSincTailError k t₀ h A (((M : ℝ) + 1) / A) := by
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (∑' n : ℤ, plattZetaWindow k t₀ h ((n : ℝ) / A) *
      (Real.sinc (Real.pi * (A * v - n)) : ℂ)) _).trans
    (add_le_add (norm_plattZetaWindow_sub_sinc_le m k hm ht₀ hh hA v)
      (norm_plattZetaSinc_sub_finite_le M k t₀ v hh hA hk))

/-- Only the retained sample values need numerical enclosures. -/
theorem norm_plattFiniteSinc_sub_le (M : ℕ) (A v : ℝ) {f q : ℤ → ℂ} {ε : ℤ → ℝ}
    (h₀ : ∀ n ∈ Finset.range (M + 1), ‖f n - q n‖ ≤ ε n)
    (h₁ : ∀ n ∈ Finset.range M, ‖f (-(n + 1)) - q (-(n + 1))‖ ≤ ε (-(n + 1))) :
    ‖plattFiniteSinc M A v f - plattFiniteSinc M A v q‖ ≤
      Fourier.symmetricSum (fun n => ε n * |Real.sinc (Real.pi * (A * v - n))|) M := by
  apply Fourier.norm_symmetricSum_sub_le M
  · intro n hn
    rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (h₀ n hn) (abs_nonneg _)
  · intro n hn
    rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (h₁ n hn) (abs_nonneg _)

/-- A complete finite interpolator encloses the true off-grid value including final rounding. -/
theorem norm_plattZetaWindow_sub_approx_finiteSinc_le (m M k : ℕ) (hm : 1 ≤ m)
    {t₀ h A : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A)
    (hk : ((k : ℝ) + 1) * h ^ 2 < (((M : ℝ) + 1) / A) ^ 2) (v : ℝ)
    {q : ℤ → ℂ} {ε : ℤ → ℝ}
    (h₀ : ∀ n ∈ Finset.range (M + 1), ‖plattZetaWindow k t₀ h ((n : ℝ) / A) - q n‖ ≤ ε n)
    (h₁ : ∀ n ∈ Finset.range M,
      ‖plattZetaWindow k t₀ h ((-(n + 1) : ℤ) / A) - q (-(n + 1))‖ ≤ ε (-(n + 1)))
    {z : ℂ} {δ : ℝ} (hz : ‖plattFiniteSinc M A v q - z‖ ≤ δ) :
    ‖plattZetaWindow k t₀ h v - z‖ ≤
      plattSincError m k t₀ h A + plattSincTailError k t₀ h A (((M : ℝ) + 1) / A) +
        Fourier.symmetricSum (fun n => ε n * |Real.sinc (Real.pi * (A * v - n))|) M + δ := by
  have he := (norm_sub_le_norm_sub_add_norm_sub (plattZetaWindow k t₀ h v)
    (plattFiniteSinc M A v (fun n => plattZetaWindow k t₀ h ((n : ℝ) / A)))
    (plattFiniteSinc M A v q)).trans (add_le_add
      (norm_plattZetaWindow_sub_finiteSinc_le m M k hm ht₀ hh hA hk v)
      (norm_plattFiniteSinc_sub_le M A v h₀ h₁))
  exact (norm_sub_le_norm_sub_add_norm_sub _ (plattFiniteSinc M A v q) _).trans (add_le_add he hz)

end

end PrimeFactorUnimodality
