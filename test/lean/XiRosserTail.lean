import PrimeFactorUnimodality.Helpers.Analytic.XiRosserSymmetry

/-! # Actual damped zero tails: convergence, endpoint multiplicity and both ordinate signs -/

namespace PrimeFactorUnimodality.Tests

open Real Filter MeasureTheory Set
open scoped Topology

example {a q u : ℝ} {P : RiemannXiDivisorZeroIndex → Prop}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u)
    (hP : ∀ p, P p → u ≤ (riemannXiDivisorZeroValue p).im) :
    Summable (fun p : {p : RiemannXiDivisorZeroIndex // P p} =>
      logDampedPower a q (riemannXiDivisorZeroValue p.1).im) :=
  summable_xi_logDampedPower_of_lower_bound ha hq hu hP

example {a q u : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u)
    (hw : exp (sqrt (a / q)) ≤ u) :
    Tendsto (fun T => (xiZeroCount T : ℝ) * logDampedPower a q T) atTop (𝓝 0) :=
  tendsto_xiZeroCount_mul_logDampedPower ha hq hu hw

example {a q u : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u)
    (hw : exp (sqrt (a / q)) ≤ u) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // u < (riemannXiDivisorZeroValue p).im},
      logDampedPower a q (riemannXiDivisorZeroValue p.1).im) =
      -(xiZeroCount u : ℝ) * logDampedPower a q u -
        ∫ t in Ioi u, (xiZeroCount t : ℝ) * logDampedPowerSlope a q t :=
  (xi_strict_damped_tail_eq_count_integral ha hq hu hw).2

example {a q u : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 10 ≤ u)
    (hw : exp (sqrt (a / q)) ≤ u) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // u < (riemannXiDivisorZeroValue p).im},
      logDampedPower a q (riemannXiDivisorZeroValue p.1).im) ≤
      xiRosserTailIntegral a q u -
        (xiZeroCountingRemainder u - (Real.log u + 17)) * logDampedPower a q u :=
  xi_strict_damped_tail_le_integral ha hq hu hw

example (f : ℝ → ℝ) (u : ℝ) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // (riemannXiDivisorZeroValue p).im = u},
      f (riemannXiDivisorZeroValue p.1).im) = (xiOrdinateMultiplicity u : ℝ) * f u :=
  tsum_xi_weight_at_ordinate f u

example {a q u : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // u ≤ (riemannXiDivisorZeroValue p).im},
      logDampedPower a q (riemannXiDivisorZeroValue p.1).im) =
      (∑' p : {p : RiemannXiDivisorZeroIndex // u < (riemannXiDivisorZeroValue p).im},
        logDampedPower a q (riemannXiDivisorZeroValue p.1).im) +
      (xiOrdinateMultiplicity u : ℝ) * logDampedPower a q u :=
  xi_closed_damped_tail_eq_strict_add_boundary ha hq hu

example {a q u : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 10 < u)
    (hw : exp (sqrt (a / q)) ≤ u) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // u ≤ (riemannXiDivisorZeroValue p).im},
      logDampedPower a q (riemannXiDivisorZeroValue p.1).im) ≤
      xiRosserTailIntegral a q u + 2 * (Real.log u + 17) * logDampedPower a q u :=
  xi_closed_damped_tail_le_integral ha hq hu hw

example {a q u : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) :
    xiRosserAbsoluteTail a q u =
      2 * ∑' p : {p : RiemannXiDivisorZeroIndex // u ≤ (riemannXiDivisorZeroValue p).im},
        logDampedPower a q (riemannXiDivisorZeroValue p.1).im :=
  xiRosserAbsoluteTail_eq_twice_positive ha hq hu

example {a q u : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 10 < u)
    (hw : exp (sqrt (a / q)) ≤ u) :
    xiRosserAbsoluteTail a q u ≤
      2 * (xiRosserTailIntegral a q u + 2 * (Real.log u + 17) * logDampedPower a q u) :=
  xiRosserAbsoluteTail_le_integral ha hq hu hw

example {u : ℝ} (hu : 1 < u) :
    Summable (fun p : {p : RiemannXiDivisorZeroIndex // u ≤ |(riemannXiDivisorZeroValue p).im|} =>
      logDampedPower 0 2 |(riemannXiDivisorZeroValue p.1).im|) :=
  summable_xi_abs_logDampedPower le_rfl le_rfl hu (fun _ hp => hp)

example {a b q u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hq : 2 ≤ q) (hu : 1 < u) :
    xiRosserAbsoluteTail b q u ≤ xiRosserAbsoluteTail a q u :=
  xiRosserAbsoluteTail_antitone_parameter ha hab hq hu

example {b q u : ℝ} (hb : 0 ≤ b) (hq : 2 ≤ q) (hu : 1 < u) :
    xiRosserAbsoluteTail b q u ≤ xiRosserAbsoluteTail 0 q u :=
  xiRosserAbsoluteTail_antitone_parameter le_rfl hb hq hu

example {a q U : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hU : 1 < U)
    (B : Finset RiemannXiDivisorZeroIndex)
    (hB : ∀ z ∈ B, U ≤ |(riemannXiDivisorZeroValue z).im|) :
    (∑ z ∈ B,
      logDampedPower a q |(riemannXiDivisorZeroValue z).im|) ≤ xiRosserAbsoluteTail a q U :=
  sum_xi_logDampedPower_le_absoluteTail ha hq hU B hB

end PrimeFactorUnimodality.Tests
