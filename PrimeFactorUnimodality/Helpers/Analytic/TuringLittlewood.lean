import PrimeFactorUnimodality.Helpers.Analytic.TuringHorizontalContinuity
import PrimeFactorUnimodality.Helpers.Analytic.TuringLittlewoodReduction

/-! # Littlewood's identity and an explicit integrated argument bound

Continuity through every zero height discharges the remaining hypothesis
of the finite-exception fundamental theorem. The complete horizontal
upper and lower bounds now give an unconditional argument-integral budget.
The closed-count identity retains the exact smooth Gamma/pole correction;
no finite Riemann-hypothesis verification or numerical signs are assumed.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Set

/-- Littlewood's identity on every positive interval, including zero ordinates and endpoints. -/
theorem integral_turingZetaArgument_eq_horizontal_sub {σ a b : ℝ}
    (hσ : 1 < σ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ T in a..b, turingZetaArgument σ T) =
      turingHorizontalIntegral b - turingHorizontalIntegral a :=
  integral_turingZetaArgument_eq_horizontal_sub_of_continuous hσ ha hab
    (continuousOn_turingHorizontalIntegral.mono (fun _ ht => ha.trans_le ht.1))

/-- The actual closed-count discrepancy has the exact horizontal and smooth-phase decomposition. -/
theorem pi_mul_integral_xiZeroCountingRemainder_eq_horizontal {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    Real.pi * (∫ T in a..b, xiZeroCountingRemainder T) =
      turingHorizontalIntegral b - turingHorizontalIntegral a +
        (∫ T in a..b, turingCountingPhase T) -
          Real.pi * (xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a) :=
  pi_mul_integral_xiZeroCountingRemainder_eq_horizontal_of_continuous ha hab
    (continuousOn_turingHorizontalIntegral.mono (fun _ ht => ha.trans_le ht.1))

/-- An explicit argument-integral budget using both complete, untruncated horizontal tails. -/
theorem abs_integral_turingZetaArgument_le {σ a b : ℝ}
    (hσ : 1 < σ) (ha : 1 ≤ a) (hab : a ≤ b) :
    |∫ T in a..b, turingZetaArgument σ T| ≤ (19 / 2 : ℝ) * Real.log (5 * b) + 95 :=
  abs_integral_turingZetaArgument_le_of_continuous hσ ha hab
    (continuousOn_turingHorizontalIntegral.mono
      (fun _ ht => lt_of_lt_of_le (by linarith : 0 < a) ht.1))

end

end PrimeFactorUnimodality
