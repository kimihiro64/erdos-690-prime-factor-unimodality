import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaEnvelope
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.ExponentialAliasing

set_option autoImplicit false

/-! # Frequency aliasing of the genuine zeta-window transform

Exact geometric sums apply to the proved contour-plus-pole envelope. The
offset margin is explicit, so a shifted frequency cannot silently retain
the central-cell margin. Convergence holds at every real offset.
-/

open scoped FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- The full periodization of the actual zeta Fourier transform. -/
def plattZetaFourierPeriodization (k : ℕ) (t₀ h A x : ℝ) : ℂ :=
  ∑' n : ℤ, 𝓕 (plattZetaWindow k t₀ h) (x + (n : ℝ) * A)

/-- The two exactly summed exponential alias budgets, with the available margin. -/
def plattZetaFourierAliasBound (m k : ℕ) (t₀ h A d : ℝ) : ℝ :=
  2 * ∑ i : Bool, plattZetaEnvelopeCoeff m k t₀ h i *
    (Real.exp (-plattZetaEnvelopeRate m i * d) /
      (1 - Real.exp (-plattZetaEnvelopeRate m i * A)))

/-- All geometric denominators are strictly positive at a positive period. -/
theorem plattZetaFourierAlias_denominator_pos (m : ℕ) {A : ℝ} (hA : 0 < A) (i : Bool) :
    0 < 1 - Real.exp (-plattZetaEnvelopeRate m i * A) := by
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have hr := plattZetaEnvelopeRate_pos m i
  nlinarith

/-- The true Fourier periodization converges at every real offset and positive period. -/
theorem summable_plattZetaFourierPeriodization (k : ℕ) {t₀ h A : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A) (x : ℝ) :
    Summable (fun n : ℤ => 𝓕 (plattZetaWindow k t₀ h) (x + (n : ℝ) * A)) :=
  Fourier.summable_lattice_of_finite_exp_bound_margin (s := Finset.univ)
    (fun i _ => plattZetaEnvelopeCoeff_nonneg 1 k (by omega) ht₀ hh i)
    (fun i _ => plattZetaEnvelopeRate_pos 1 i) hA (d := A - |x|) (by linarith)
    (norm_fourier_plattZetaWindow_le_envelope 1 k (by omega) ht₀ hh)

/-- The complete frequency-alias error is bounded at the actual offset margin. -/
theorem norm_plattZetaFourierPeriodization_sub_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h A x d : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A)
    (hx : |x| + d ≤ A) :
    ‖plattZetaFourierPeriodization k t₀ h A x - 𝓕 (plattZetaWindow k t₀ h) x‖ ≤
      plattZetaFourierAliasBound m k t₀ h A d :=
  Fourier.norm_periodization_sub_le_of_finite_exp_bound_margin
    (s := Finset.univ) (fun i _ => plattZetaEnvelopeCoeff_nonneg m k hm ht₀ hh i)
    (fun i _ => plattZetaEnvelopeRate_pos m i) hA hx
    (norm_fourier_plattZetaWindow_le_envelope m k hm ht₀ hh)

end

end PrimeFactorUnimodality
