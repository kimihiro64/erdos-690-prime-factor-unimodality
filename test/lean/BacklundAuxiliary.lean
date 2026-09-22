import PrimeFactorUnimodality.Helpers.Analytic.BacklundRealZeros

/-! # Recurrence, the patched pole, and actual Backlund crossings

Powers returning to the right half-plane include torsion points and negative
real numbers. The source auxiliary function is entire even at its translated
patched poles. Root counts preserve the nonzero-centre prerequisite.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter Metric Set
open scoped Topology

example : ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧
    Tendsto (fun n => I ^ q n) atTop (𝓝 1) :=
  Complex.exists_pow_tendsto_one_of_norm_eq_one (by simp)

example : ∃ᶠ n : ℕ in atTop, ‖(-2 : ℂ)‖ ^ n / 2 ≤ ((-2 : ℂ) ^ n).re :=
  Complex.frequently_half_norm_pow_le_re_pow (by norm_num)

example (n : ℕ) : backlundAuxiliary 0 n 1 = 1 := by
  simp [backlundAuxiliary, Backlund.zetaSurrogate]

example (T : ℝ) (n : ℕ) : AnalyticAt ℂ (backlundAuxiliary T n) (1 - T * I) :=
  (differentiable_backlundAuxiliary T n).analyticAt _

example (T σ : ℝ) (n : ℕ) : backlundAuxiliary T n σ = 0 ↔
    (Backlund.zetaSurrogate ((σ : ℂ) + T * I) ^ n).re = 0 :=
  backlundAuxiliary_ofReal_eq_zero_iff T σ n

example {T σ r : ℝ} {n : ℕ} (hr : 0 ≤ r) (hc : backlundAuxiliary T n σ ≠ 0) :
    (backlundRealZeros T n σ r).Finite :=
  finite_backlundRealZeros hr hc

example {T σ r : ℝ} {n : ℕ} (hr : 0 ≤ r) (hc : backlundAuxiliary T n σ ≠ 0) :
    (backlundRealZeroCount T n σ r : ℝ) ≤ backlundAuxiliaryZeroMass T n σ r :=
  backlundRealZeroCount_le_mass hr hc

example (T : ℝ) : ∃ᶠ n : ℕ in atTop,
    ‖Backlund.zetaSurrogate ((2 : ℂ) + T * I)‖ ^ n / 2 ≤ ‖backlundAuxiliary T n 2‖ :=
  frequently_backlundAuxiliary_centre_lower (by norm_num) T

example {σ T r R M : ℝ} (hσ : 1 < σ) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hp : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    ∃ᶠ n : ℕ in atTop, (backlundRealZeroCount T n σ r : ℝ) ≤
      ((n : ℝ) * Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) + Real.log 2) /
        Real.log (R / r) :=
  frequently_backlundRealZeroCount_le hσ hr hrR hM hp hm

end

end PrimeFactorUnimodality.Tests
