import PrimeFactorUnimodality.Helpers.Analytic.DusartEndpointElementary

/-! # Reduced-cutoff interfaces and real-endpoint regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real Set MeasureTheory

example {x : ℝ} (hx : (1440000000000 : ℝ) ≤ x) :
    exp (-(1 / 2) * Real.log x) ≤ (1 / 1200000 : ℝ) := by
  exact PrimeFactorUnimodality.dusartEndpoint_half_log_decay_le hx

example {x : ℝ} (hx : (1440000000000 : ℝ) ≤ x) :
    (1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)) / x ≤ (4 / 1440000000000 : ℝ) := by
  exact PrimeFactorUnimodality.dusartEndpoint_correction_le hx



end

end PrimeFactorUnimodality.Tests
