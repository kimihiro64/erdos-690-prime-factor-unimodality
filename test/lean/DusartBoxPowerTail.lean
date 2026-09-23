import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPowerTail

/-! # Regression checks for explicit endpoint estimates and their hypotheses -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real intervalIntegral

example (m : ℕ) {h x T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 10 < T) :
    ‖dusartBoxXiHighSum m h x T‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        xiRosserPowerTailBound (m + 4 : ℕ) T :=
  norm_dusartBoxXiHighSum_le_power m hh hx hT

example (m : ℕ) {s x T : ℝ}
    (hs : 0 < s) (hx : 1 < x) (hT : 10 < T) :
    ‖dusartBoxXiHighSum m (s * x) x T‖ / x ≤
      (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
        xiRosserPowerTailBound (m + 4 : ℕ) T :=
  norm_dusartBoxXiHighSum_div_le_power m hs hx hT

end PrimeFactorUnimodality.Tests
