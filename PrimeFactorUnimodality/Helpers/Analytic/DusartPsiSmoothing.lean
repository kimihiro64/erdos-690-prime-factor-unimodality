import Mathlib.NumberTheory.Chebyshev
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverage

/-! # Recovering the Chebyshev error from iterated averages

This is the monotone averaging step of Dusart's HDR (2022), section 2.2,
Theorem 35. We average `psi(t) - t` directly, so the logarithmic and trivial
zero terms are not hidden: they must be included when estimating these
averages by an explicit formula. The exact smoothing loss is `m * h / 2`.
Every natural averaging order is allowed, including the identity at zero.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev intervalIntegral

/-- The actual averaged Chebyshev error, with the linear main term subtracted. -/
def dusartPsiAverageError (m : ℕ) (h x : ℝ) : ℝ :=
  iteratedBoxAverage h m (fun t => ψ t - t) x

/-- The two adjacent averages enclose the pointwise error, including at jumps of psi. -/
theorem dusart_psi_error_between_averages (m : ℕ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    dusartPsiAverageError m h (x - m * h) - m * h / 2 ≤ ψ x - x ∧
      ψ x - x ≤ dusartPsiAverageError m h x + m * h / 2 :=
  sub_id_bounds_of_iteratedBoxAverage hh psi_mono m x

/-- Absolute control of both actual averages gives a pointwise absolute error bound. -/
theorem dusart_abs_psi_error_le_of_averages (m : ℕ) {h x E : ℝ} (hh : 0 < h)
    (hleft : |dusartPsiAverageError m h (x - m * h)| ≤ E)
    (hright : |dusartPsiAverageError m h x| ≤ E) :
    |ψ x - x| ≤ E + m * h / 2 := by
  have h := dusart_psi_error_between_averages m hh x
  rcases abs_le.mp hleft with ⟨hl, _⟩
  rcases abs_le.mp hright with ⟨_, hr⟩
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

/-- At scale `h = x * delta`, the normalized smoothing loss is exactly `m * delta / 2`. -/
theorem dusart_relative_psi_error_le_of_averages (m : ℕ) {δ x ε : ℝ}
    (hx : 0 < x) (hδ : 0 < δ)
    (hleft : |dusartPsiAverageError m (x * δ) (x - m * (x * δ))| ≤ x * ε)
    (hright : |dusartPsiAverageError m (x * δ) x| ≤ x * ε) :
    |ψ x / x - 1| ≤ ε + m * δ / 2 := by
  have h := dusart_abs_psi_error_le_of_averages m (mul_pos hx hδ) hleft hright
  have he : ψ x / x - 1 = (ψ x - x) / x := by field_simp
  rw [he, abs_div, abs_of_pos hx]
  apply (div_le_iff₀ hx).mpr
  nlinarith only [h]

end

end PrimeFactorUnimodality
