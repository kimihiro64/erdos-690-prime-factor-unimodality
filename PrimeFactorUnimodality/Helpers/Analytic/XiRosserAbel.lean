import PrimeFactorUnimodality.Helpers.Analytic.XiHeightTail
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingImproper
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDampedTail

/-! # Infinite Abel identities for the actual damped xi tail

The previously proved inverse-square summability and finite-sublevel Abel
limit supply convergence and the vanishing upper boundary. No numerical
counting envelope or assumed integrability is needed for this identity.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real Filter MeasureTheory Set
open scoped Topology

/-- Any actual zero subset with a positive lower ordinate has a summable damped kernel. -/
theorem summable_xi_logDampedPower_of_lower_bound {a q u : ℝ}
    {P : RiemannXiDivisorZeroIndex → Prop}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u)
    (hP : ∀ p, P p → u ≤ (riemannXiDivisorZeroValue p).im) :
    Summable (fun p : {p : RiemannXiDivisorZeroIndex // P p} =>
      logDampedPower a q (riemannXiDivisorZeroValue p.1).im) := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hs := summable_xi_height_inv_sq (P := P)
    hu0 0 (fun p hp => by
      simp only [zero_sub, neg_sq]
      exact pow_le_pow_left₀ hu0.le (hP p hp) 2)
  simp only [zero_sub, neg_sq] at hs
  exact Summable.of_nonneg_of_le (fun p => (logDampedPower_pos _ _ _).le)
    (fun p => logDampedPower_le_inv_sq ha hq (hu.trans_le (hP p.1 p.2))) hs

/-- In particular the strict positive-ordinate tail is summable. -/
theorem summable_xi_logDampedPower {a q u : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) :
    Summable (fun p : {p : RiemannXiDivisorZeroIndex // u < (riemannXiDivisorZeroValue p).im} =>
      logDampedPower a q (riemannXiDivisorZeroValue p.1).im) :=
  summable_xi_logDampedPower_of_lower_bound ha hq hu (fun _ hp => hp.le)

/-- The actual counting boundary vanishes beyond the turning height. -/
theorem tendsto_xiZeroCount_mul_logDampedPower {a q u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) (hw : exp (sqrt (a / q)) ≤ u) :
    Tendsto (fun T => (xiZeroCount T : ℝ) * logDampedPower a q T) atTop (𝓝 0) := by
  apply tendsto_xiZeroCount_mul_of_antitone (lt_trans zero_lt_one hu).le
    (summable_xi_logDampedPower ha hq hu)
    (fun _ _ => (logDampedPower_pos _ _ _).le)
    (antitoneOn_logDampedPower_after ha (by linarith) hu hw)
    (tendsto_logDampedPower_atTop ha hq)

/-- The strict weighted tail equals its integrable counting integral with the lower boundary. -/
theorem xi_strict_damped_tail_eq_count_integral {a q u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) (hw : exp (sqrt (a / q)) ≤ u) :
    IntegrableOn (fun t => (xiZeroCount t : ℝ) * logDampedPowerSlope a q t) (Ioi u) ∧
      (∑' p : {p : RiemannXiDivisorZeroIndex // u < (riemannXiDivisorZeroValue p).im},
        logDampedPower a q (riemannXiDivisorZeroValue p.1).im) =
        -(xiZeroCount u : ℝ) * logDampedPower a q u -
          ∫ t in Ioi u, (xiZeroCount t : ℝ) * logDampedPowerSlope a q t := by
  apply xi_strict_tail_eq_integral_of_count_boundary (lt_trans zero_lt_one hu).le
    (summable_xi_logDampedPower ha hq hu)
    (fun t ht => hasDerivAt_logDampedPower (hu.trans_le ht))
    (fun b => (continuousOn_logDampedPowerSlope
      (fun t ht => hu.trans_le ht.1)).integrableOn_Icc)
    (fun t ht => logDampedPowerSlope_nonpos_after ha (by linarith) (hu.trans ht)
      (hw.trans ht.le))
    (tendsto_xiZeroCount_mul_logDampedPower ha hq hu hw)

end

end PrimeFactorUnimodality
