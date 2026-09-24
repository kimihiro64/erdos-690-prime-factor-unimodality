import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxReflectedFrozen
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserFrozenAverage

/-! # Reflected tail bounds for the actual normalized psi average

Only the high-zero contribution changes. The proved low-zero mass and the
negative-even and endpoint corrections are retained, then the shared
spectral assembly supplies the actual average throughout the later ray.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real intervalIntegral

/-- The complete reflected normalized average at one reference point. -/
def dusartReflectedRelativeBudget (m : ℕ) (s x R p a H δ : ℝ) : ℝ :=
  ((1 + (m + 3 : ℕ) * s) * exp (-δ * Real.log x)) * xiLowReciprocalNormBound a H δ +
    (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
      dusartReflectedClosedTail (Real.log x) R (m + 4 : ℕ) p H +
    (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x

/-- One reflected endpoint value bounds every later actual normalized psi average. -/
theorem abs_dusartPsiAverageError_div_le_reflected_frozen (m : ℕ) {s x x₀ R p a H δ : ℝ}
    (hs : 0 < s) (hx₀ : 1 < x₀) (hx : x₀ ≤ x) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x₀ / R) / (m + 4 : ℕ))) ≤ H)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartReflectedRelativeBudget m s x₀ R p a H δ := by
  have hl := norm_dusartBox_low_div_le_frozen m hs hx₀ hx ha haH hδ hgap
  have hu := norm_dusartBoxXiHighSum_div_le_reflected_frozen m hs hx₀ hx hR hp hpq
    (by linarith) hpeak hreg
  exact (abs_dusartPsiAverageError_div_le_of_zero_bounds m hs (hx₀.trans_le hx) hl hu).trans
    (add_le_add le_rfl (dusartBox_relative_correction_le hx₀ hx))

end

end PrimeFactorUnimodality
