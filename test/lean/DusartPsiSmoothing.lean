import PrimeFactorUnimodality.Helpers.Analytic.DusartPsiSmoothing

/-! # Iterated smoothing regressions

Check arbitrary order, the zero-order identity, exact constant and linear
averages, and the pointwise bound for the actual discontinuous psi function.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Chebyshev intervalIntegral

example (h x : ℝ) (f : ℝ → ℝ) : iteratedBoxAverage h 0 f x = f x := rfl

example {h : ℝ} (hh : h ≠ 0) (m : ℕ) (c x : ℝ) :
    iteratedBoxAverage h m (fun _ => c) x = c := iteratedBoxAverage_const hh m c x

example {h : ℝ} (hh : 0 < h) (m : ℕ) (x : ℝ) :
    iteratedBoxAverage h m id x = x + m * h / 2 := by
  have he := iteratedBoxAverage_sub_id hh monotone_id m x
  have hz : (fun t : ℝ => id t - t) = fun _ => 0 := by funext t; simp
  rw [hz, iteratedBoxAverage_const hh.ne'] at he
  linarith

example {h : ℝ} (hh : 0 < h) (m : ℕ) : Monotone (iteratedBoxAverage h m ψ) :=
  monotone_iteratedBoxAverage hh psi_mono m

example (m : ℕ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    dusartPsiAverageError m h (x - m * h) - m * h / 2 ≤ ψ x - x ∧
      ψ x - x ≤ dusartPsiAverageError m h x + m * h / 2 :=
  dusart_psi_error_between_averages m hh x

example (h x : ℝ) : dusartPsiAverageError 0 h x = ψ x - x := rfl

example {h x E : ℝ} (hh : 0 < h)
    (hl : |dusartPsiAverageError 2 h (x - 2 * h)| ≤ E)
    (hr : |dusartPsiAverageError 2 h x| ≤ E) : |ψ x - x| ≤ E + h := by
  have he := dusart_abs_psi_error_le_of_averages 2 hh hl hr
  norm_num at he ⊢
  linarith

example (m : ℕ) {δ x ε : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hl : |dusartPsiAverageError m (x * δ) (x - m * (x * δ))| ≤ x * ε)
    (hr : |dusartPsiAverageError m (x * δ) x| ≤ x * ε) :
    |ψ x / x - 1| ≤ ε + m * δ / 2 :=
  dusart_relative_psi_error_le_of_averages m hx hδ hl hr

end

end PrimeFactorUnimodality.Tests
