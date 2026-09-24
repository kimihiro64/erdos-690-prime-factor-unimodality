import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.ThetaSieveSteps

set_option autoImplicit false

/-! # Complete theta-prefix traces with retained boundary states

Each transition certifies the new count and theta enclosure once. Before the
consumer threshold only transport is required; every later cell checks both
strict theta margins. Explicit final-state equality prevents missing endpoints.
-/

namespace PrimeFactorUnimodality

/-- The exact theta requirements on a half-open integer range. -/
def DusartTailThetaSegment (left right : Nat) : Prop :=
  ∀ q : Nat, 3501 ≤ q → left ≤ q → q < right → TailThetaAt q

/-- Adjacent ranges share one endpoint without leaving a hole in coverage. -/
theorem DusartTailThetaSegment.append {left middle right : Nat}
    (first : DusartTailThetaSegment left middle)
    (second : DusartTailThetaSegment middle right) : DusartTailThetaSegment left right := by
  intro q hq hl hr
  by_cases hm : q < middle
  · exact first q hq hl hm
  · exact second q hq (by omega) hr

/-- Check the exact final checkpoint as well as every local count, log and theta margin. -/
def checkDusartThetaTrace (N k bits : Nat) (start finish : DusartThetaState) :
    List DusartThetaSieveStep → Bool
  | [] => decide (start = finish)
  | row :: rest =>
      row.check N k bits start &&
        (decide (row.next.point ≤ 3501) || row.checkTail start) &&
          checkDusartThetaTrace N k bits row.next finish rest

/-- Accepted traces preserve the true final state and prove every required intermediate point. -/
theorem checkDusartThetaTrace_sound {N k bits : Nat}
    (sieve : PrimeCert.Sieve.IsSieve N bits) {start finish : DusartThetaState}
    (state : start.Valid) {rows : List DusartThetaSieveStep}
    (valid : checkDusartThetaTrace N k bits start finish rows = true) :
    finish.Valid ∧ DusartTailThetaSegment start.point finish.point := by
  induction rows generalizing start with
  | nil =>
    simp only [checkDusartThetaTrace, decide_eq_true_eq] at valid
    subst finish
    exact ⟨state, by intro q _ hl hr; omega⟩
  | cons row rest ih =>
    simp only [checkDusartThetaTrace, Bool.and_eq_true] at valid
    have nextState := row.provides sieve state valid.1.1
    have tailProof := ih nextState valid.2
    refine ⟨tailProof.1, ?_⟩
    intro q hq hl hr
    by_cases inCell : q < row.next.point
    · have margin : row.checkTail start = true := by
        have hm := valid.1.2
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hm
        rcases hm with small | margin
        · omega
        · exact margin
      have step := valid.1.1
      simp only [DusartThetaSieveStep.check, Bool.and_eq_true, decide_eq_true_eq] at step
      obtain ⟨_, _, hsu, _, hpu, _, _⟩ := step.1
      exact row.provides_tail state nextState
        (row.upperPower.log_le_upper nextState.1 hsu hpu) margin hq hl inCell.le
    · exact tailProof.2 q hq (by omega) hr

/-- The elementary initial checkpoint counts two primes, with small rational log enclosures. -/
def dusartThetaSeed : DusartThetaState :=
  ⟨3, 2, 1791759 / 1000000, 1791761 / 1000000⟩

/-- The seed is obtained from log two and log three, with no numerical oracle. -/
theorem dusartThetaSeed_valid : dusartThetaSeed.Valid := by
  have theta : Chebyshev.theta (3 : Real) = Real.log 2 + Real.log 3 := by
    have h := Chebyshev.theta_eq_sum_primesLE_log 3
    have hp : Nat.primesLE 3 = {2, 3} := by decide
    rw [hp] at h
    norm_num at h
    exact h
  constructor
  · decide
  constructor
  · decide +kernel
  simp only [dusartThetaSeed, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat]
  rw [theta]
  constructor
  · linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
  · linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

end PrimeFactorUnimodality
