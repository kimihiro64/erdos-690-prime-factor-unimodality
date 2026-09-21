import PrimeFactorUnimodality.Helpers.Analytic.DecayToLogFourth
import PrimeFactorUnimodality.Helpers.Analytic.DusartProof
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows
import PrimeFactorUnimodality.Helpers.Analytic.MediumPNT
import PrimeFactorUnimodality.Helpers.Analytic.ZetaExplicitBounds


set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-!
# Closed explicit theta estimates

Implementation owner: Luna.

This module must prove and export
`PrimeFactorUnimodality.wangCrapis_thetaBounds : HasDusartThetaBounds`
from the repository's proved zero-free-region, Chebyshev, logarithm-envelope,
and compact finite low-endpoint machinery.  It must not import a prepackaged
Dusart theorem or add an assumption-backed provider.

The exact proof obligations and dependency order are recorded in
`LEAN_COMPLETION_HANDOFF.md`.  The finite singleton seed below is closed; it
does not claim to be the global provider.
-/

/-! Closed singleton seed for the finite theta assembler. -/

theorem wangCrapis_thetaPrefix :
    HasDusartSymmetricThetaBoundsBelow (2 : Real) := by
  exact hasDusartSymmetricThetaBoundsBelow_mono (by norm_num)
    (hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows
      dusartThetaEndpointRow_three_cover)

theorem wangCrapis_thetaPrefix_three :
    HasDusartSymmetricThetaBoundsBelow (3 : Real) := by
  exact hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows
    dusartThetaEndpointRow_three_cover

theorem wangCrapis_thetaBounds_lower_2_3
    {x : Real} (hx : 2 < x) (hx3 : x ≤ 3) :
    x * (1 - (12323 / 10000 : Real) / Real.log x) <
      Chebyshev.theta x := by
  have hxpos : 0 < x := by linarith
  have hfloor : ⌊x⌋₊ = 2 := by
    have hlo : 2 ≤ ⌊x⌋₊ := Nat.le_floor (le_of_lt hx)
    have hhi : ⌊x⌋₊ ≤ 2 := Nat.floor_le_of_le hx3
    omega
  have htheta : Chebyshev.theta x = Real.log 2 := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hfloor, theta_two_eq_log_two]
  rw [htheta]
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog_le : Real.log x ≤ Real.log 3 :=
    Real.log_le_log hxpos hx3
  have hlog_lt : Real.log x < (12323 : Real) / 10000 := by
    have hthree : Real.log 3 < (11 : Real) / 10 := by
      exact Real.log_three_lt_d9
    linarith
  have hcoef : 1 - (12323 / 10000 : Real) / Real.log x < 0 := by
    apply sub_neg.mpr
    apply (lt_div_iff₀ hlogpos).2
    linarith
  have hleft : x * (1 - (12323 / 10000 : Real) / Real.log x) < 0 :=
    mul_neg_of_pos_of_neg hxpos hcoef
  have hlog2pos : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  linarith

theorem wangCrapis_thetaBounds_upper_0_3
    {x : Real} (hx : 0 < x) (hx3 : x ≤ 3) :
    Chebyshev.theta x - x < x / 36260 := by
  have htheta_nonneg : 0 ≤ Chebyshev.theta x := Chebyshev.theta_nonneg x
  by_cases hlt : x < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two hlt]
    positivity
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 3 :=
      Chebyshev.theta_mono hx3
    have htheta3 : Chebyshev.theta (3 : Real) =
        Real.log 2 + Real.log 3 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE_log 3
      have hp : Nat.primesLE 3 = {2, 3} := by decide
      rw [hp] at hsum
      simpa using hsum
    rw [htheta3] at htheta_le
    have hlog2lt : Real.log (2 : Real) < 1 := by
      nlinarith [Real.log_two_lt_d9]
    have hlog3lt : Real.log (3 : Real) < (11 : Real) / 10 :=
      Real.log_three_lt_d9
    have hright : 0 < x / 36260 := by positivity
    linarith

theorem wangCrapis_thetaBoundsBelow_3 :
    HasDusartSymmetricThetaBoundsBelow (3 : Real) := by
  constructor
  · intro x hx hx3
    exact wangCrapis_thetaBounds_upper_0_3 hx hx3
  · intro x hx hx3
    exact wangCrapis_thetaBounds_lower_2_3 hx hx3

theorem wangCrapis_thetaBoundsBelow_4 :
    HasDusartSymmetricThetaBoundsBelow (4 : Real) := by
  constructor
  · intro x hx hx4
    by_cases hsmall : x ≤ 3
    · exact (wangCrapis_thetaBoundsBelow_3).1 x hx hsmall
    · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 4 :=
        Chebyshev.theta_mono hx4
      have hx3 : (3 : Real) < x := lt_of_not_ge hsmall
      have htheta4 : Chebyshev.theta (4 : Real) =
          Real.log 2 + Real.log 3 := by
        have hsum := Chebyshev.theta_eq_sum_primesLE_log 4
        have hp : Nat.primesLE 4 = {2, 3} := by decide
        rw [hp] at hsum
        simpa using hsum
      rw [htheta4] at htheta_le
      have htheta4_lt : Chebyshev.theta (4 : Real) < (9 : Real) / 5 := by
        rw [htheta4]
        nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
      have hx_pos : 0 < x := by linarith
      have hright : 0 < x / 36260 := by positivity
      nlinarith
  · intro x hx hx4
    by_cases hsmall : x ≤ 3
    · exact (wangCrapis_thetaBoundsBelow_3).2 x hx hsmall
    · have hx_pos : 0 < x := by linarith
      have hx3 : (3 : Real) < x := lt_of_not_ge hsmall
      have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
      have hlogupper : Real.log x < (7 : Real) / 5 := by
        have hlog4 : Real.log x ≤ Real.log 4 :=
          Real.log_le_log hx_pos hx4
        rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num,
          Real.log_pow] at hlog4
        nlinarith [Real.log_two_lt_d9]
      have hcoef : (3 : Real) / 5 <
          (12323 / 10000 : Real) / Real.log x := by
        apply (lt_div_iff₀ hlogpos).2
        nlinarith [hlogupper]
      have htheta3 : Chebyshev.theta (3 : Real) =
          Real.log 2 + Real.log 3 := by
        have hsum := Chebyshev.theta_eq_sum_primesLE_log 3
        have hp : Nat.primesLE 3 = {2, 3} := by decide
        rw [hp] at hsum
        simpa using hsum
      have htheta_lower : Chebyshev.theta 3 > (8 : Real) / 5 := by
        rw [htheta3]
        nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
      have htheta_mono : Chebyshev.theta 3 ≤ Chebyshev.theta x :=
        Chebyshev.theta_mono hx3.le
      have hbound :
          x * (1 - (12323 / 10000 : Real) / Real.log x) <
            (2 : Real) / 5 * x := by
        nlinarith
      nlinarith

theorem wangCrapis_thetaBoundsBelow_5 :
    HasDusartSymmetricThetaBoundsBelow (5 : Real) := by
  constructor
  · intro x hx hx5
    by_cases hx4 : x ≤ 4
    · exact (wangCrapis_thetaBoundsBelow_4).1 x hx hx4
    · have hx4' : (4 : Real) < x := lt_of_not_ge hx4
      have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 5 :=
        Chebyshev.theta_mono hx5
      have htheta5 : Chebyshev.theta (5 : Real) =
          Real.log 2 + Real.log 3 + Real.log 5 := by
        have hsum := Chebyshev.theta_eq_sum_primesLE_log 5
        have hp : Nat.primesLE 5 = {2, 3, 5} := by decide
        rw [hp] at hsum
        simpa [add_assoc] using hsum
      rw [htheta5] at htheta_le
      have htheta5_lt : Chebyshev.theta (5 : Real) < (7 : Real) / 2 := by
        rw [htheta5]
        nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
          LogTables.log_5_lt]
      have hx_pos : 0 < x := by linarith
      have hright : 0 < x / 36260 := by positivity
      nlinarith
  · intro x hx hx5
    by_cases hx4 : x ≤ 4
    · exact (wangCrapis_thetaBoundsBelow_4).2 x hx hx4
    · have hx_pos : 0 < x := by linarith
      have hx4' : (4 : Real) < x := lt_of_not_ge hx4
      have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
      have hlogupper : Real.log x < (17 : Real) / 10 := by
        have hlog5 : Real.log x ≤ Real.log 5 :=
          Real.log_le_log hx_pos hx5
        exact hlog5.trans_lt LogTables.log_5_lt
      have hcoef : (7 : Real) / 10 <
          (12323 / 10000 : Real) / Real.log x := by
        apply (lt_div_iff₀ hlogpos).2
        nlinarith [hlogupper]
      have htheta4_eq : Chebyshev.theta (4 : Real) =
          Real.log 2 + Real.log 3 := by
        have hsum := Chebyshev.theta_eq_sum_primesLE_log 4
        have hp : Nat.primesLE 4 = {2, 3} := by decide
        rw [hp] at hsum
        simpa using hsum
      have htheta4 : Chebyshev.theta (4 : Real) > (8 : Real) / 5 := by
        rw [htheta4_eq]
        nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
      have htheta_mono : Chebyshev.theta 4 ≤ Chebyshev.theta x :=
        Chebyshev.theta_mono hx4'.le
      have hbound :
          x * (1 - (12323 / 10000 : Real) / Real.log x) <
            (3 : Real) / 10 * x := by
        nlinarith
      nlinarith

theorem wangCrapis_thetaBoundsBelow_6 :
    HasDusartSymmetricThetaBoundsBelow (6 : Real) := by
  constructor
  · intro x hx hx6
    by_cases hx5 : x ≤ 5
    · exact (wangCrapis_thetaBoundsBelow_5).1 x hx hx5
    · have hx5' : (5 : Real) < x := lt_of_not_ge hx5
      have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 6 :=
        Chebyshev.theta_mono hx6
      have htheta6 : Chebyshev.theta (6 : Real) =
          Real.log 2 + Real.log 3 + Real.log 5 := by
        have hsum := Chebyshev.theta_eq_sum_primesLE_log 6
        have hp : Nat.primesLE 6 = {2, 3, 5} := by decide
        rw [hp] at hsum
        simpa [add_assoc] using hsum
      rw [htheta6] at htheta_le
      have htheta6_lt : Chebyshev.theta (6 : Real) < (7 : Real) / 2 := by
        rw [htheta6]
        nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
          LogTables.log_5_lt]
      have hx_pos : 0 < x := by linarith
      have hright : 0 < x / 36260 := by positivity
      nlinarith
  · intro x hx hx6
    by_cases hx5 : x ≤ 5
    · exact (wangCrapis_thetaBoundsBelow_5).2 x hx hx5
    · have hx_pos : 0 < x := by linarith
      have hx5' : (5 : Real) < x := lt_of_not_ge hx5
      have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
      have hlogupper : Real.log x < (9 : Real) / 5 := by
        have hlog6 : Real.log x ≤ Real.log 6 :=
          Real.log_le_log hx_pos hx6
        rw [show (6 : Real) = 2 * 3 by norm_num,
          Real.log_mul (by norm_num) (by norm_num)] at hlog6
        nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
      have hcoef : (2 : Real) / 3 <
          (12323 / 10000 : Real) / Real.log x := by
        apply (lt_div_iff₀ hlogpos).2
        nlinarith [hlogupper]
      have htheta5_eq : Chebyshev.theta (5 : Real) =
          Real.log 2 + Real.log 3 + Real.log 5 := by
        have hsum := Chebyshev.theta_eq_sum_primesLE_log 5
        have hp : Nat.primesLE 5 = {2, 3, 5} := by decide
        rw [hp] at hsum
        simpa [add_assoc] using hsum
      have htheta5 : Chebyshev.theta (5 : Real) > 3 := by
        rw [htheta5_eq]
        nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9,
          Real.log_five_gt_d9]
      have htheta_mono : Chebyshev.theta 5 ≤ Chebyshev.theta x :=
        Chebyshev.theta_mono hx5'.le
      have hbound :
          x * (1 - (12323 / 10000 : Real) / Real.log x) <
            (1 : Real) / 3 * x := by
        nlinarith
      nlinarith

/-! The next low endpoint contains no new analytic ingredient: between `6`
    and `7` the theta sum is still the sum over `2, 3, 5`, while the value at
    `7` gives a convenient monotonic upper endpoint.  Keep this prefix
    separate so later finite-row construction can start at `7`. -/
theorem wangCrapis_thetaBoundsBelow_7 :
    HasDusartSymmetricThetaBoundsBelow (7 : Real) := by
  constructor
  · intro x hx hx7
    by_cases hx6 : x ≤ 6
    · exact (wangCrapis_thetaBoundsBelow_6).1 x hx hx6
    · have hx6' : (6 : Real) < x := lt_of_not_ge hx6
      have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 7 :=
        Chebyshev.theta_mono hx7
      have htheta7 : Chebyshev.theta (7 : Real) =
          Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 := by
        have hsum := Chebyshev.theta_eq_sum_primesLE 7
        have hp : Nat.primesLE 7 = {2, 3, 5, 7} := by decide
        rw [hp] at hsum
        simpa [add_assoc] using hsum
      rw [htheta7] at htheta_le
      have htheta7_lt : Chebyshev.theta (7 : Real) < (6 : Real) := by
        rw [htheta7]
        nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
          Real.log_five_lt_d9, LogTables.log_7_lt]
      have hright : 0 < x / 36260 := by positivity
      nlinarith
  · intro x hx hx7
    by_cases hx6 : x ≤ 6
    · exact (wangCrapis_thetaBoundsBelow_6).2 x hx hx6
    · have hx6' : (6 : Real) < x := lt_of_not_ge hx6
      have hx_pos : 0 < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
      have hlogupper : Real.log x < (2 : Real) := by
        have hlog7 : Real.log x ≤ Real.log 7 :=
          Real.log_le_log hx_pos hx7
        exact lt_of_le_of_lt hlog7 (by
          simpa using (LogTables.log_7_lt.trans (by norm_num :
            (1.946044 : Real) < 2)))
      have hcoef : (3 : Real) / 5 <
          (12323 / 10000 : Real) / Real.log x := by
        apply (lt_div_iff₀ hlogpos).2
        nlinarith [hlogupper]
      have htheta6_eq : Chebyshev.theta (6 : Real) =
          Real.log 2 + Real.log 3 + Real.log 5 := by
        have hsum := Chebyshev.theta_eq_sum_primesLE 6
        have hp : Nat.primesLE 6 = {2, 3, 5} := by decide
        rw [hp] at hsum
        simpa [add_assoc] using hsum
      have htheta6 : Chebyshev.theta (6 : Real) > 3 := by
        rw [htheta6_eq]
        nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9,
          Real.log_five_gt_d9]
      have htheta_mono : Chebyshev.theta 6 ≤ Chebyshev.theta x :=
        Chebyshev.theta_mono hx6'.le
      have hbound :
          x * (1 - (12323 / 10000 : Real) / Real.log x) <
            (2 : Real) / 5 * x := by
        nlinarith
      have hupper : Chebyshev.theta x - x < x / 36260 := by
        have htheta_nonneg : 0 ≤ Chebyshev.theta x :=
          Chebyshev.theta_nonneg x
        have htheta7 : Chebyshev.theta x < 6 := by
          have htheta7' : Chebyshev.theta x ≤ Chebyshev.theta 7 :=
            Chebyshev.theta_mono hx7
          have hsum := Chebyshev.theta_eq_sum_primesLE 7
          have hp : Nat.primesLE 7 = {2, 3, 5, 7} := by decide
          rw [hp] at hsum
          rw [← hsum] at htheta7'
          nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
            Real.log_five_lt_d9, LogTables.log_7_lt]
        nlinarith
      have hlogcoef : (1 : Real) / 36260 <
          (12323 / 10000 : Real) / Real.log x := by
        apply (lt_div_iff₀ hlogpos).2
        nlinarith [hlogupper]
      have hscaled := mul_lt_mul_of_pos_right hlogcoef hx_pos
      have hupper_error : Chebyshev.theta x - x <
          (12323 / 10000 : Real) * x / Real.log x := by
        nlinarith
      apply (abs_lt).2
      constructor
      · nlinarith [hbound, htheta_mono, htheta6]
      · exact hupper_error

theorem wangCrapis_theta_lower_error_below_seven
    {x : Real} (hx : 2 < x) (hx7 : x ≤ 7) :
    |Chebyshev.theta x - x| <
      (12323 / 10000 : Real) * x / Real.log x := by
  have hprefix := wangCrapis_thetaBoundsBelow_7
  have hupper := hprefix.1 x (by linarith) hx7
  have hlower := hprefix.2 x hx hx7
  have hx_pos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogupper : Real.log x < (2 : Real) := by
    have hlog7 : Real.log x ≤ Real.log 7 :=
      Real.log_le_log hx_pos hx7
    exact lt_of_le_of_lt hlog7 (by
      simpa using (LogTables.log_7_lt.trans (by norm_num :
        (1.946044 : Real) < 2)))
  have hcoef : (1 : Real) / 36260 <
      (12323 / 10000 : Real) / Real.log x := by
    apply (lt_div_iff₀ hlogpos).2
    nlinarith [hlogupper]
  have hscaled := mul_lt_mul_of_pos_right hcoef hx_pos
  have herror : x / 36260 <
      (12323 / 10000 : Real) * x / Real.log x := by
    nlinarith
  apply (abs_lt).2
  constructor
  · nlinarith
  · exact hupper.trans herror

theorem wangCrapis_theta_lower_error_below_six
    {x : Real} (hx : 2 < x) (hx6 : x ≤ 6) :
    |Chebyshev.theta x - x| <
      (12323 / 10000 : Real) * x / Real.log x := by
  have hprefix := wangCrapis_thetaBoundsBelow_6
  have hupper := hprefix.1 x (by linarith) hx6
  have hlower := hprefix.2 x hx hx6
  have hx_pos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogupper : Real.log x < (9 : Real) / 5 := by
    have hlog6 : Real.log x ≤ Real.log 6 :=
      Real.log_le_log hx_pos hx6
    rw [show (6 : Real) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)] at hlog6
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have hcoef : (1 : Real) / 36260 <
      (12323 / 10000 : Real) / Real.log x := by
    apply (lt_div_iff₀ hlogpos).2
    nlinarith [hlogupper]
  have hscaled := mul_lt_mul_of_pos_right hcoef hx_pos
  have herror : x / 36260 <
      (12323 / 10000 : Real) * x / Real.log x := by
    nlinarith
  apply (abs_lt).2
  constructor
  · nlinarith
  · exact hupper.trans herror

/-! The same direct low-endpoint computation supplies the strict prefix used
    by the Schoenfeld split. -/
theorem wangCrapis_strictThetaPrefix_three :
    HasStrictThetaUpperBelow (3 : Real) := by
  intro x hx hx3
  by_cases hsmall : x < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
    linarith
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 3 :=
      Chebyshev.theta_mono hx3
    have htheta3 : Chebyshev.theta (3 : Real) =
        Real.log 2 + Real.log 3 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE_log 3
      have hp : Nat.primesLE 3 = {2, 3} := by decide
      rw [hp] at hsum
      simpa using hsum
    rw [htheta3] at htheta_le
    have hlog2lt : Real.log (2 : Real) < (9 : Real) / 10 :=
      Real.log_two_lt_d9
    have hlog3lt : Real.log (3 : Real) < (11 : Real) / 10 :=
      Real.log_three_lt_d9
    linarith

/-! The same prime-break decomposition extends the strict upper prefix to
    seven.  The endpoint bounds are kept local to this small source prefix;
    later large intervals must still provide their own verified rows. -/
theorem wangCrapis_strictThetaPrefix_seven :
    HasStrictThetaUpperBelow (7 : Real) := by
  intro x hx hx7
  by_cases hthree : x ≤ 3
  · exact wangCrapis_strictThetaPrefix_three x hx hthree
  by_cases hfive : x < 5
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 3 := by
      exact Chebyshev.theta_mono (by linarith)
    have htheta3 : Chebyshev.theta (3 : Real) =
        Real.log 2 + Real.log 3 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE 3
      have hp : Nat.primesLE 3 = {2, 3} := by decide
      rw [hp] at hsum
      simpa using hsum
    rw [htheta3] at htheta_le
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
  by_cases hseven : x < 7
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 5 := by
      exact Chebyshev.theta_mono (by linarith)
    have htheta5 : Chebyshev.theta (5 : Real) =
        Real.log 2 + Real.log 3 + Real.log 5 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE 5
      have hp : Nat.primesLE 5 = {2, 3, 5} := by decide
      rw [hp] at hsum
      simpa [add_assoc] using hsum
    rw [htheta5] at htheta_le
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
      Real.log_five_lt_d9]
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 7 :=
      Chebyshev.theta_mono hx7
    have htheta7 : Chebyshev.theta (7 : Real) =
        Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE 7
      have hp : Nat.primesLE 7 = {2, 3, 5, 7} := by decide
      rw [hp] at hsum
      simpa [add_assoc] using hsum
    rw [htheta7] at htheta_le
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
      Real.log_five_lt_d9, LogTables.log_7_lt]

theorem wangCrapis_strictThetaPrefix_eleven :
    HasStrictThetaUpperBelow (11 : Real) := by
  intro x hx hx11
  by_cases hseven : x ≤ 7
  · exact wangCrapis_strictThetaPrefix_seven x hx hseven
  by_cases heleven : x < 11
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 7 := by
      exact Chebyshev.theta_mono (by linarith)
    have htheta7 : Chebyshev.theta (7 : Real) =
        Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE_log 7
      have hp : Nat.primesLE 7 = {2, 3, 5, 7} := by decide
      rw [hp] at hsum
      simpa [add_assoc] using hsum
    rw [htheta7] at htheta_le
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
      Real.log_five_lt_d9, LogTables.log_7_lt]
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 11 :=
      Chebyshev.theta_mono hx11
    have htheta11 : Chebyshev.theta (11 : Real) =
        Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE_log 11
      have hp : Nat.primesLE 11 = {2, 3, 5, 7, 11} := by decide
      rw [hp] at hsum
      simpa [add_assoc] using hsum
    rw [htheta11] at htheta_le
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
      Real.log_five_lt_d9, LogTables.log_7_lt,
      ElementaryLogBounds.log_11_lt]

theorem wangCrapis_strictThetaPrefix_thirteen :
    HasStrictThetaUpperBelow (13 : Real) := by
  intro x hx hx13
  by_cases heleven : x ≤ 11
  · exact wangCrapis_strictThetaPrefix_eleven x hx heleven
  by_cases hthirteen : x < 13
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 11 := by
      exact Chebyshev.theta_mono (by linarith)
    have htheta11 : Chebyshev.theta (11 : Real) =
        Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE_log 11
      have hp : Nat.primesLE 11 = {2, 3, 5, 7, 11} := by decide
      rw [hp] at hsum
      simpa [add_assoc] using hsum
    rw [htheta11] at htheta_le
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
      Real.log_five_lt_d9, LogTables.log_7_lt,
      ElementaryLogBounds.log_11_lt]
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 13 :=
      Chebyshev.theta_mono hx13
    have htheta13 : Chebyshev.theta (13 : Real) =
        Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 +
          Real.log 11 + Real.log 13 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE_log 13
      have hp : Nat.primesLE 13 = {2, 3, 5, 7, 11, 13} := by decide
      rw [hp] at hsum
      simpa [add_assoc] using hsum
    rw [htheta13] at htheta_le
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
      Real.log_five_lt_d9, LogTables.log_7_lt,
      ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt]

/-! The same exact prime-break argument extends the direct strict prefix
    through the next two prime endpoints. -/
theorem wangCrapis_strictThetaPrefix_nineteen :
    HasStrictThetaUpperBelow (19 : Real) := by
  intro x hx hx19
  by_cases hthirteen : x ≤ 13
  · exact wangCrapis_strictThetaPrefix_thirteen x hx hthirteen
  by_cases hseventeen : x < 17
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 13 := by
      exact Chebyshev.theta_mono (by linarith)
    have htheta13 : Chebyshev.theta (13 : Real) =
        Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 +
          Real.log 11 + Real.log 13 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE_log 13
      have hp : Nat.primesLE 13 = {2, 3, 5, 7, 11, 13} := by decide
      rw [hp] at hsum
      simpa [add_assoc] using hsum
    rw [htheta13] at htheta_le
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
      Real.log_five_lt_d9, LogTables.log_7_lt,
      ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt]
  by_cases hnineteen : x < 19
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 17 := by
      exact Chebyshev.theta_mono (by linarith)
    have htheta17 : Chebyshev.theta (17 : Real) =
        Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 +
          Real.log 11 + Real.log 13 + Real.log 17 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE_log 17
      have hp : Nat.primesLE 17 = {2, 3, 5, 7, 11, 13, 17} := by decide
      rw [hp] at hsum
      simpa [add_assoc] using hsum
    rw [htheta17] at htheta_le
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
      Real.log_five_lt_d9, LogTables.log_7_lt,
      ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
      ElementaryLogBounds.log_17_lt]
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 19 :=
      Chebyshev.theta_mono hx19
    have htheta19 : Chebyshev.theta (19 : Real) =
        Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 +
          Real.log 11 + Real.log 13 + Real.log 17 + Real.log 19 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE_log 19
      have hp : Nat.primesLE 19 = {2, 3, 5, 7, 11, 13, 17, 19} := by decide
      rw [hp] at hsum
      simpa [add_assoc] using hsum
    rw [htheta19] at htheta_le
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
      Real.log_five_lt_d9, LogTables.log_7_lt,
      ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
      ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt]

theorem wangCrapis_strictThetaPrefix_twenty_nine :
    HasStrictThetaUpperBelow (29 : Real) := by
  intro x hx hx29
  by_cases hnineteen : x ≤ 19
  · exact wangCrapis_strictThetaPrefix_nineteen x hx hnineteen
  by_cases htwentythree : x < 23
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 19 := by
      exact Chebyshev.theta_mono (by linarith)
    have htheta19 : Chebyshev.theta (19 : Real) =
        Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 +
          Real.log 11 + Real.log 13 + Real.log 17 + Real.log 19 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE_log 19
      have hp : Nat.primesLE 19 = {2, 3, 5, 7, 11, 13, 17, 19} := by decide
      rw [hp] at hsum
      simpa [add_assoc] using hsum
    rw [htheta19] at htheta_le
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
      Real.log_five_lt_d9, LogTables.log_7_lt,
      ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
      ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt]
  by_cases htwentynine : x < 29
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 23 := by
      exact Chebyshev.theta_mono (by linarith)
    have htheta23 : Chebyshev.theta (23 : Real) =
        Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 +
          Real.log 11 + Real.log 13 + Real.log 17 + Real.log 19 +
          Real.log 23 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE_log 23
      have hp : Nat.primesLE 23 = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by decide
      rw [hp] at hsum
      simpa [add_assoc] using hsum
    rw [htheta23] at htheta_le
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
      Real.log_five_lt_d9, LogTables.log_7_lt,
      ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
      ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
      ElementaryLogBounds.log_23_lt]
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 29 :=
      Chebyshev.theta_mono hx29
    have htheta29 : Chebyshev.theta (29 : Real) =
        Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 +
          Real.log 11 + Real.log 13 + Real.log 17 + Real.log 19 +
          Real.log 23 + Real.log 29 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE_log 29
      have hp : Nat.primesLE 29 =
          {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by decide
      rw [hp] at hsum
      simpa [add_assoc] using hsum
    rw [htheta29] at htheta_le
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
      Real.log_five_lt_d9, LogTables.log_7_lt,
      ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
      ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
      ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt]

/-! The fixed explicit-formula input is exported at the theta boundary so the
    eventual psi/theta tail proof consumes the constructed estimate rather than
    the package's existential placeholder. -/
end

end

end PrimeFactorUnimodality
