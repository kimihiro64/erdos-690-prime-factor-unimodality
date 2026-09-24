import PrimeFactorUnimodality.Helpers.Analytic.PlattFiniteSinc
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaSignTransport

/-! Finite off-grid interpolation retains all tails and reaches the existing xi sign theorem. -/

open PrimeFactorUnimodality

example (k : ℕ) (t₀ v : ℝ) {h A : ℝ} (hh : 0 < h) (hA : 0 < A) :
    Summable (fun n : ℤ => plattZetaWindow k t₀ h ((n : ℝ) / A) *
      (Real.sinc (Real.pi * (A * v - n)) : ℂ)) :=
  summable_plattZetaWindow_sinc k t₀ v hh hA

example (i : Bool) : 0 < 1 - Real.exp (-plattSincTailRate 0 1 2 i / 3) :=
  plattSincTail_denominator_pos 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) i

example (M : ℕ) (A : ℝ) (q : ℤ → ℂ) :
    plattFiniteSinc M A 0 q = Fourier.symmetricSum
      (fun n => q n * (Real.sinc (Real.pi * -(n : ℝ)) : ℂ)) M := by
  simp [plattFiniteSinc]

example (m M : ℕ) (hm : 1 ≤ m) {t₀ h A : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A)
    (hk : h ^ 2 < (((M : ℝ) + 1) / A) ^ 2) (v : ℝ)
    {q : ℤ → ℂ} {ε : ℤ → ℝ}
    (h₀ : ∀ n ∈ Finset.range (M + 1), ‖plattZetaWindow 0 t₀ h ((n : ℝ) / A) - q n‖ ≤ ε n)
    (h₁ : ∀ n ∈ Finset.range M,
      ‖plattZetaWindow 0 t₀ h ((-(n + 1) : ℤ) / A) - q (-(n + 1))‖ ≤ ε (-(n + 1)))
    {z : ℂ} {δ : ℝ} (hz : ‖plattFiniteSinc M A v q - z‖ ≤ δ)
    (hmarg : plattSincError m 0 t₀ h A + plattSincTailError 0 t₀ h A (((M : ℝ) + 1) / A) +
      Fourier.symmetricSum (fun n => ε n * |Real.sinc (Real.pi * (A * v - n))|) M + δ < z.re) :
    xiCriticalLineValue (v + t₀) < 0 := by
  have he := norm_plattZetaWindow_sub_approx_finiteSinc_le m M 0 hm ht₀ hh hA
    (by simpa using hk) v h₀ h₁ hz
  rw [norm_sub_rev] at he
  exact xiCriticalLineValue_neg_of_platt_approx he hmarg
