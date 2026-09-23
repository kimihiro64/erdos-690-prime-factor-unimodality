import PrimeFactorUnimodality.Helpers.Analytic.XiRosserCutoff

/-! # Both ordinate signs in the closed Rosser tail

The existing conjugation equivalence preserves every divisor label and
identifies the negative tail with the positive one. The absolute-height
series is exactly twice the positive series, including zeros at the cutoff.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real Set

/-- Any subset beyond an absolute-height cutoff has a summable damped kernel. -/
theorem summable_xi_abs_logDampedPower {a q u : ℝ} {P : RiemannXiDivisorZeroIndex → Prop}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u)
    (hP : ∀ p, P p → u ≤ |(riemannXiDivisorZeroValue p).im|) :
    Summable (fun p : {p : RiemannXiDivisorZeroIndex // P p} =>
      logDampedPower a q |(riemannXiDivisorZeroValue p.1).im|) := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hs := summable_xi_height_inv_sq (P := P) hu0 0 (fun p hp => by
    simpa only [zero_sub, neg_sq, sq_abs] using pow_le_pow_left₀ hu0.le (hP p hp) 2)
  simp only [zero_sub, neg_sq] at hs
  apply Summable.of_nonneg_of_le (fun p => (logDampedPower_pos _ _ _).le) _ hs
  intro p
  simpa only [sq_abs] using logDampedPower_le_inv_sq ha hq (hu.trans_le (hP p.1 p.2))

/-- The complete closed absolute-height damped series. -/
def xiRosserAbsoluteTail (a q u : ℝ) : ℝ :=
  ∑' p : {p : RiemannXiDivisorZeroIndex // u ≤ |(riemannXiDivisorZeroValue p).im|},
    logDampedPower a q |(riemannXiDivisorZeroValue p.1).im|

/-- A fixed closed tail decreases when its damping parameter increases. -/
theorem xiRosserAbsoluteTail_antitone_parameter {a b q u : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hq : 2 ≤ q) (hu : 1 < u) :
    xiRosserAbsoluteTail b q u ≤ xiRosserAbsoluteTail a q u := by
  apply (summable_xi_abs_logDampedPower (ha.trans hab) hq hu (fun _ hp => hp)).tsum_le_tsum
    _ (summable_xi_abs_logDampedPower ha hq hu (fun _ hp => hp))
  intro p
  exact logDampedPower_antitone_parameter hab (hu.trans_le p.2)


/-- Conjugation pairs the whole closed tail, not just distinct zero heights. -/
theorem xiRosserAbsoluteTail_eq_twice_positive {a q u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 1 < u) :
    xiRosserAbsoluteTail a q u =
      2 * ∑' p : {p : RiemannXiDivisorZeroIndex // u ≤ (riemannXiDivisorZeroValue p).im},
        logDampedPower a q (riemannXiDivisorZeroValue p.1).im := by
  let P : Set RiemannXiDivisorZeroIndex := {p | u ≤ (riemannXiDivisorZeroValue p).im}
  let N : Set RiemannXiDivisorZeroIndex := {p | u ≤ -(riemannXiDivisorZeroValue p).im}
  let f (p : RiemannXiDivisorZeroIndex) := logDampedPower a q |(riemannXiDivisorZeroValue p).im|
  have hp : Summable (fun p : P => f p.1) :=
    summable_xi_abs_logDampedPower ha hq hu (fun _ h => h.trans (le_abs_self _))
  have hn : Summable (fun p : N => f p.1) :=
    summable_xi_abs_logDampedPower ha hq hu (fun _ h => h.trans (neg_le_abs _))
  have hd : Disjoint P N := by
    rw [Set.disjoint_left]
    intro p hp hn
    change u ≤ _ at hp
    change u ≤ -_ at hn
    linarith
  have hU : {p : RiemannXiDivisorZeroIndex | u ≤ |(riemannXiDivisorZeroValue p).im|} = P ∪ N := by
    ext p
    change u ≤ |(riemannXiDivisorZeroValue p).im| ↔
      u ≤ (riemannXiDivisorZeroValue p).im ∨ u ≤ -(riemannXiDivisorZeroValue p).im
    exact le_abs
  have hc := (xiPositiveNegativeHeightEquiv u).tsum_eq (fun p : N => f p.1)
  have hvalue (p : P) : f ((xiPositiveNegativeHeightEquiv u p).1) = f p.1 := by
    change logDampedPower a q |(riemannXiDivisorZeroValue (riemannXiDivisorConjugation p.1)).im| = _
    simp only [riemannXiDivisorZeroValue_conjugation, conj_im, abs_neg, f]
  simp_rw [hvalue] at hc
  change (∑' p : P, f p.1) = ∑' p : N, f p.1 at hc
  unfold xiRosserAbsoluteTail
  change (∑' p : ({p : RiemannXiDivisorZeroIndex |
      u ≤ |(riemannXiDivisorZeroValue p).im|} : Set RiemannXiDivisorZeroIndex), f p.1) = _
  rw [hU, Summable.tsum_union_disjoint (f := f) hd hp hn, ← hc, ← two_mul]
  congr 1
  apply tsum_congr
  intro p
  exact congrArg (logDampedPower a q) (abs_of_pos ((lt_trans zero_lt_one hu).trans_le p.2))

/-- The full two-sided closed tail has the Rosser integral bound with no missing cutoff term. -/
theorem xiRosserAbsoluteTail_le_integral {a q u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hu : 10 < u) (hw : exp (sqrt (a / q)) ≤ u) :
    xiRosserAbsoluteTail a q u ≤
      2 * (xiRosserTailIntegral a q u + 2 * (Real.log u + 17) * logDampedPower a q u) := by
  rw [xiRosserAbsoluteTail_eq_twice_positive ha hq (by linarith)]
  exact mul_le_mul_of_nonneg_left (xi_closed_damped_tail_le_integral ha hq hu hw) (by norm_num)

/-- Any finite set beyond the cutoff fits in the complete multiplicity-counted tail. -/
theorem sum_xi_logDampedPower_le_absoluteTail {a q U : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hU : 1 < U)
    (B : Finset RiemannXiDivisorZeroIndex)
    (hB : ∀ z ∈ B, U ≤ |(riemannXiDivisorZeroValue z).im|) :
    (∑ z ∈ B,
      logDampedPower a q |(riemannXiDivisorZeroValue z).im|) ≤ xiRosserAbsoluteTail a q U := by
  classical
  let e : {p : RiemannXiDivisorZeroIndex // p ∈ B} →
      {p : RiemannXiDivisorZeroIndex // U ≤ |(riemannXiDivisorZeroValue p).im|} :=
    fun p => ⟨p.1, hB p.1 p.2⟩
  have he : Function.Injective e := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun r => r.val) h
  rw [← B.tsum_subtype (fun p => logDampedPower a q |(riemannXiDivisorZeroValue p).im|)]
  exact Summable.tsum_le_tsum_of_inj e he
    (fun _ _ => (logDampedPower_pos _ _ _).le) (fun _ => le_rfl)
    (summable_of_hasFiniteSupport (Set.toFinite _))
    (summable_xi_abs_logDampedPower ha hq hU (fun _ hp => hp))

end

end PrimeFactorUnimodality
