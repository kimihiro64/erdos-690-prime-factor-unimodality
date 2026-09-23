import PrimeFactorUnimodality.Helpers.Analytic.XiHeightTailEndpoint
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserTailBound

/-! # Restoring the cutoff atoms in the Rosser tail

A weight depending only on ordinate is constant on every finite divisor
fiber. The closed tail therefore equals the strict tail plus its complete
cutoff multiplicity. Combining that multiplicity with the signed counting
boundary replaces the closed count by the strict count before bounding it.
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Real Set

/-- Every ordinate weight sums exactly to its value times the finite multiplicity. -/
theorem tsum_xi_weight_at_ordinate (f : ℝ → ℝ) (u : ℝ) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // (riemannXiDivisorZeroValue p).im = u},
      f (riemannXiDivisorZeroValue p.1).im) = (xiOrdinateMultiplicity u : ℝ) * f u := by
  let : Fintype {p : RiemannXiDivisorZeroIndex // (riemannXiDivisorZeroValue p).im = u} :=
    (finite_xi_divisor_im_eq u).fintype
  calc
    _ = ∑' _p : {p : RiemannXiDivisorZeroIndex // (riemannXiDivisorZeroValue p).im = u},
        f u := tsum_congr (fun p => congrArg f p.2)
    _ = _ := by simp [xiOrdinateMultiplicity, Nat.card_eq_fintype_card]

/-- The closed positive-ordinate damped tail is absolutely summable. -/
theorem summable_xi_closed_logDampedPower {a q u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) :
    Summable (fun p : {p : RiemannXiDivisorZeroIndex // u ≤ (riemannXiDivisorZeroValue p).im} =>
      logDampedPower a q (riemannXiDivisorZeroValue p.1).im) :=
  summable_xi_logDampedPower_of_lower_bound ha hq hu (fun _ hp => hp)

/-- All cutoff labels are added back, with no assumption that the height avoids zeros. -/
theorem xi_closed_damped_tail_eq_strict_add_boundary {a q u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // u ≤ (riemannXiDivisorZeroValue p).im},
      logDampedPower a q (riemannXiDivisorZeroValue p.1).im) =
      (∑' p : {p : RiemannXiDivisorZeroIndex // u < (riemannXiDivisorZeroValue p).im},
        logDampedPower a q (riemannXiDivisorZeroValue p.1).im) +
      (xiOrdinateMultiplicity u : ℝ) * logDampedPower a q u := by
  let S : Set RiemannXiDivisorZeroIndex := {p | u < (riemannXiDivisorZeroValue p).im}
  let B : Set RiemannXiDivisorZeroIndex := {p | (riemannXiDivisorZeroValue p).im = u}
  let f (p : RiemannXiDivisorZeroIndex) := logDampedPower a q (riemannXiDivisorZeroValue p).im
  have hs : Summable (fun p : S => f p.1) := summable_xi_logDampedPower ha hq hu
  have hb : Summable (fun p : B => f p.1) := (finite_xi_divisor_im_eq u).summable f
  have hd : Disjoint S B := by
    rw [Set.disjoint_left]
    intro p hp hb
    exact (ne_of_lt hp) hb.symm
  have he : {p : RiemannXiDivisorZeroIndex | u ≤ (riemannXiDivisorZeroValue p).im} = S ∪ B := by
    ext p
    change u ≤ _ ↔ u < _ ∨ _ = u
    exact le_iff_lt_or_eq.trans (or_congr_right eq_comm)
  change (∑' p : ({p : RiemannXiDivisorZeroIndex |
      u ≤ (riemannXiDivisorZeroValue p).im} : Set RiemannXiDivisorZeroIndex), f p.1) = _
  rw [he, Summable.tsum_union_disjoint (f := f) hd hs hb]
  exact congrArg (fun z => (∑' p : S, f p.1) + z)
    (tsum_xi_weight_at_ordinate (logDampedPower a q) u)

/-- The closed tail has no residual cutoff-multiplicity cost in its envelope bound. -/
theorem xi_closed_damped_tail_le_integral {a q u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 10 < u) (hw : exp (sqrt (a / q)) ≤ u) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // u ≤ (riemannXiDivisorZeroValue p).im},
      logDampedPower a q (riemannXiDivisorZeroValue p.1).im) ≤
      xiRosserTailIntegral a q u + 2 * (Real.log u + 17) * logDampedPower a q u := by
  rw [xi_closed_damped_tail_eq_strict_add_boundary ha hq (by linarith)]
  have hs := xi_strict_damped_tail_le_integral ha hq hu.le hw
  have hc : (xiZeroCount u : ℝ) = (xiStrictZeroCount u : ℝ) + xiOrdinateMultiplicity u := by
    exact_mod_cast xiZeroCount_eq_strict_add_multiplicity (by linarith : 0 < u)
  have hE := (abs_le.mp (abs_xiStrictZeroCount_sub_mainTerm_le_log_add hu)).1
  unfold xiZeroCountingRemainder at hs
  rw [hc] at hs
  have hn := mul_nonneg
    (show 0 ≤ (xiStrictZeroCount u : ℝ) - xiZeroCountingMainTerm u + (Real.log u + 17) by
      linarith) (logDampedPower_pos a q u).le
  nlinarith only [hs, hn]

end

end PrimeFactorUnimodality
