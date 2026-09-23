import PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapParameters
import PrimeFactorUnimodality.Helpers.Analytic.ZetaZeroFreeBounded

/-! # Discharging the low-height input of the initial constant-56 bootstrap

The bounded-strip region controls every zero below the starting height
at the largest harmonic cutoff. Together with the existing high region,
this supplies both location inputs for the first elementary bootstrap.
Its numerical margins, and subsequent improved-region stages, are separate.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The first bootstrap's low-height premise follows from the bounded initial region. -/
theorem xi_low_re_le_kadiri_initial_sigma {n : ℕ} (hn : 1 ≤ n) {H T : ℝ}
    (hH : 0 ≤ H) (hT : 10 ^ 9 ≤ T) (p : RiemannXiDivisorZeroIndex)
    (hp : |(riemannXiDivisorZeroValue p).im| < T) :
    (riemannXiDivisorZeroValue p).re ≤ kadiriBootstrapSigma 56 n H T := by
  have hcut := le_kadiri_harmonic_cutoff hn hH (by linarith : 0 ≤ T)
  have hg := xi_zero_gap_bounded (hT.trans hcut) (riemannXiDivisorZeroValue_eq_zero p)
    (hp.le.trans hcut)
  unfold kadiriBootstrapSigma
  linarith

end

end PrimeFactorUnimodality
