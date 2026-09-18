import PrimeFactorUnimodality.Proof.LargeRange.TailNumerics
import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime

set_option autoImplicit false

/-! # Uniform elementary error bounds above the optimized cutoff -/

namespace PrimeFactorUnimodality

noncomputable section

/-! The exact prime-pair input consumed by the uniform CRT construction.  It
is stated separately from the analytic theorem that supplies it, so the final
tail assembly has a transparent and auditable interface. -/
def HasUniformTailPrimePair : Prop :=
  ∀ r : Nat, 38000 ≤ r →
    ∃ qPrev q : Nat,
      ConsecutivePrimes qPrev q ∧ 3301 ≤ qPrev ∧
      (491 / 500 : Real) * r / Real.log r < q ∧
      (q : Real) < (2519 / 2500 : Real) *
        ((491 / 500 : Real) * r / Real.log r) ∧
      (491 / 500 : Real) * r / Real.log r <
        (2519 / 2500 : Real) * qPrev

theorem log_3301_gt : (81 : Real) / 10 < Real.log 3301 := by
  have power_lt : (2 : Real) ^ 41 * 3 ^ 11 < 3301 ^ 5 := by norm_num
  have logged := Real.log_lt_log (by positivity) power_lt
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow,
    Real.log_pow, Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

theorem log_gt_81_div_10_of_3301_le {x : Real} (hx : 3301 ≤ x) :
    (81 : Real) / 10 < Real.log x := by
  exact log_3301_gt.trans_le (Real.log_le_log (by norm_num) hx)

/-- Above `3301`, Dusart's relative short-interval error is below `1/125`.
The division is discharged only after proving the logarithmic denominator
positive. -/
theorem shortIntervalError_lt_one_div_125 {x : Real} (hx : 3301 ≤ x) :
    1 / (2 * (Real.log x) ^ 2) < (1 : Real) / 125 := by
  have logLower := log_gt_81_div_10_of_3301_le hx
  have logPos : 0 < Real.log x := by linarith
  have denominatorPos : 0 < 2 * (Real.log x) ^ 2 := by positivity
  have denominatorLarge : (125 : Real) < 2 * (Real.log x) ^ 2 := by
    nlinarith [sq_nonneg (Real.log x - 81 / 10)]
  exact one_div_lt_one_div_of_lt (by norm_num) denominatorLarge

theorem shortIntervalFactor_lt_126_div_125 {x : Real} (hx : 3301 ≤ x) :
    1 + 1 / (2 * (Real.log x) ^ 2) < (126 : Real) / 125 := by
  linarith [shortIntervalError_lt_one_div_125 hx]

private theorem log_3473_gt : (407 : Real) / 50 < Real.log 3473 := by
  have powerLt : (2 : Real) ^ 7 * 3 ^ 3 < 3473 := by norm_num
  have logged := Real.log_lt_log (by positivity) powerLt
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at logged
  rw [Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

private theorem shortIntervalFactor_lt_2519_div_2500 {x : Real} (hx : 3473 ≤ x) :
    1 + 1 / (2 * (Real.log x) ^ 2) < (2519 : Real) / 2500 := by
  have logLower := log_3473_gt.trans_le (Real.log_le_log (by norm_num) hx)
  have logPos : 0 < Real.log x := by linarith
  have denominatorPos : 0 < 2 * (Real.log x) ^ 2 := by positivity
  have errorBound : 1 / (2 * (Real.log x) ^ 2) < (19 : Real) / 2500 := by
    rw [div_lt_iff₀ denominatorPos]
    nlinarith [sq_nonneg (Real.log x - 407 / 50)]
  linarith

/-- The selected consecutive primes have fully rational relative bounds.
This is the arithmetic interface used by the later uniform-tail estimates. -/
theorem exists_tail_consecutive_primes_rational
    (shortInterval : HasDusartShortIntervalPrime) {r : Nat} (hr : 38000 ≤ r) :
    ∃ qPrev q : Nat,
      ConsecutivePrimes qPrev q ∧ 3301 ≤ qPrev ∧
      (491 / 500 : Real) * r / Real.log r < q ∧
      (q : Real) < (2519 / 2500 : Real) *
        ((491 / 500 : Real) * r / Real.log r) ∧
      (491 / 500 : Real) * r / Real.log r <
        (2519 / 2500 : Real) * qPrev := by
  obtain ⟨qPrev, q, consecutive, prevLarge, scaleLtQ, qUpper, scalePrev⟩ :=
    exists_tail_consecutive_primes shortInterval hr
  let x : Real := (491 / 500 : Real) * r / Real.log r
  have xLarge : (3301 : Real) ≤ x := by
    dsimp only [x]
    linarith [tailScale_gt_3500 hr]
  have xPos : 0 < x := by linarith
  have prevLargeReal : (3301 : Real) ≤ qPrev := by exact_mod_cast prevLarge
  have xSharper : (3473 : Real) ≤ x := by linarith [tailScale_gt_3500 hr]
  have oldPrevFactor := shortIntervalFactor_lt_126_div_125 prevLargeReal
  have prevPos : (0 : Real) < qPrev := by positivity
  have oldScaled := mul_lt_mul_of_pos_left oldPrevFactor prevPos
  have prev3473 : 3473 ≤ qPrev := by
    have : (3472 : Real) < qPrev := by
      have bound := scalePrev.trans (by simpa only [mul_comm] using oldScaled)
      nlinarith [tailScale_gt_3500 hr]
    exact_mod_cast this
  have qFactor := shortIntervalFactor_lt_2519_div_2500 xSharper
  have prevFactor := shortIntervalFactor_lt_2519_div_2500
    (show (3473 : Real) ≤ qPrev by exact_mod_cast prev3473)
  refine ⟨qPrev, q, consecutive, prevLarge, scaleLtQ, ?_, ?_⟩
  · have := mul_lt_mul_of_pos_left qFactor xPos
    dsimp only [x] at this ⊢
    nlinarith
  · have := mul_lt_mul_of_pos_left prevFactor prevPos
    nlinarith

theorem hasUniformTailPrimePair_of_shortInterval
    (shortInterval : HasDusartShortIntervalPrime) :
    HasUniformTailPrimePair := by
  intro r hr
  exact exists_tail_consecutive_primes_rational shortInterval hr

theorem hasUniformTailPrimePair_of_logCubedShortInterval
    (shortInterval : HasLogCubedShortIntervalPrime) :
    HasUniformTailPrimePair :=
  hasUniformTailPrimePair_of_shortInterval
    (hasDusartShortIntervalPrime_of_logCubed shortInterval)

end

end PrimeFactorUnimodality
