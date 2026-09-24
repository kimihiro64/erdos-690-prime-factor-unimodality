import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxReflectedPointwise

/-! # Reflected high-tail and complete pointwise interfaces -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real intervalIntegral

example (m : ℕ) {h x : ℝ} {z : ℂ} (hh : 0 < h) (hx : 1 < x)
    (hγ : 0 < |z.im|) (hline : z.re = 1 / 2) :
    ‖iteratedBoxAverageComplex h (m + 3) (fun t => (t : ℂ) ^ z / z) x‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        (exp (-(1 / 2) * Real.log x) * logDampedPower 0 (m + 4 : ℕ) |z.im|) :=
  norm_dusartBox_atom_le_half_power m hh hx hγ (by linarith) hline.le

example (m : ℕ) {s x x₀ p : ℝ} (hs : 0 < s) (hx₀ : 0 < x₀) (hx : x₀ ≤ x)
    (hl₀ : 1 < x₀ * (1 - (m + 3 : ℕ) * s))
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (hlow : ∀ z ∈ xiLowHeightIndices 170000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hpeak : exp (sqrt ((Real.log x₀ / 6) / (m + 4 : ℕ))) ≤ 170000000)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, 170000000 ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |Chebyshev.psi x - x| / x ≤ dusartReflectedFrozenPsiBound m s x₀ 6 p 10 170000000 (1 / 2) :=
  abs_psi_sub_div_le_reflected_frozen m hs hx₀ hx hl₀ (by norm_num) hp hpq
    (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] using hlow) hpeak hreg

end

end PrimeFactorUnimodality.Tests
