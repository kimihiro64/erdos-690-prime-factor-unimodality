/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedPrimeKernel

/-!
# The single turning point of the smoothed prime kernel

For each t >= 4752 and X >= 1000 there is a point m in [1000,X]
where the derivative changes from nonnegative to nonpositive. The right
sign condition uses (m,X], so the increasing-only endpoint case is included.
-/

set_option autoImplicit false

namespace Mertens

open Real

noncomputable def kernelTurnExpression (t u : Real) : Real := t * log u - t - u

theorem kernelTurnExpression_hasDerivAt (t u : Real) (hu : 0 < u) :
    HasDerivAt (kernelTurnExpression t) (t / u - 1) u := by
  unfold kernelTurnExpression
  convert! (((hasDerivAt_log hu.ne').const_mul t).sub_const t).sub
    (hasDerivAt_id' u) using 1 <;> ring

theorem kernelTurnExpression_monotone (t : Real) (ht : 4752 <= t) :
    MonotoneOn (kernelTurnExpression t) (Set.Icc 1000 t) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 1000 t)
  next =>
    intro u hu
    have hup : 0 < u := by have h := hu.1; linarith
    exact (kernelTurnExpression_hasDerivAt t u hup).continuousAt.continuousWithinAt
  next =>
    intro u hu
    have hup : 0 < u := by simp at hu; linarith [hu.1]
    exact (kernelTurnExpression_hasDerivAt t u hup).differentiableAt.differentiableWithinAt
  next =>
    intro u hu
    simp at hu
    have hup : 0 < u := by linarith [hu.1]
    rw [(kernelTurnExpression_hasDerivAt t u hup).deriv]
    have heq : t / u * u = t := by field_simp
    have hdiv : 1 <= t / u :=
      le_of_mul_le_mul_right (by rw [one_mul, heq]; exact hu.2.le) hup
    linarith

theorem kernelTurnExpression_antitone (t : Real) (ht : 4752 <= t) :
    AntitoneOn (kernelTurnExpression t) (Set.Ici t) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici t)
  next =>
    intro u hu
    have hup : 0 < u := by change t <= u at hu; linarith
    exact (kernelTurnExpression_hasDerivAt t u hup).continuousAt.continuousWithinAt
  next =>
    intro u hu
    have hup : 0 < u := by simp at hu; linarith
    exact (kernelTurnExpression_hasDerivAt t u hup).differentiableAt.differentiableWithinAt
  next =>
    intro u hu
    simp at hu
    have hup : 0 < u := by linarith
    rw [(kernelTurnExpression_hasDerivAt t u hup).deriv]
    have heq : t / u * u = t := by field_simp
    have hdiv : t / u <= 1 :=
      le_of_mul_le_mul_right (by rw [heq, one_mul]; exact hu.le) hup
    linarith

theorem kernelTurnExpression_at_1000_pos (t : Real) (ht : 4752 <= t) :
    0 < kernelTurnExpression t 1000 := by
  have hl := log_gt_three_from_1000 1000 (by norm_num)
  have hm := mul_pos (show 0 < t by linarith) (show 0 < log (1000 : Real) - 3 by linarith)
  unfold kernelTurnExpression
  nlinarith only [hm, ht]

theorem kernelTurnExpression_at_self_pos (t : Real) (ht : 4752 <= t) :
    0 < kernelTurnExpression t t := by
  have hl := log_gt_three_from_1000 t (by linarith)
  have hm := mul_pos (show 0 < t by linarith) (show 0 < log t - 3 by linarith)
  unfold kernelTurnExpression
  nlinarith only [hm, ht]

theorem kernelTurnExpression_nonneg_of_le (t v u : Real) (ht : 4752 <= t)
    (hu : 1000 <= u) (huv : u <= v) (hv : 0 <= kernelTurnExpression t v) :
    0 <= kernelTurnExpression t u := by
  by_cases hut : u <= t
  case pos =>
    have hm := kernelTurnExpression_monotone t ht
      (show Set.Icc 1000 t 1000 from And.intro le_rfl (by linarith))
      (show Set.Icc 1000 t u from And.intro hu hut) hu
    exact (kernelTurnExpression_at_1000_pos t ht).le.trans hm
  case neg =>
    have htu : t <= u := le_of_lt (lt_of_not_ge hut)
    have hm := kernelTurnExpression_antitone t ht htu (htu.trans huv) huv
    exact hv.trans hm

theorem smoothedKernel_turn (t X : Real) (ht : 4752 <= t) (hX : 1000 <= X) :
    Exists (fun m : Real => And (1000 <= m) (And (m <= X)
      (And (forall u, 1000 <= u -> u <= m -> 0 <= smoothedKernelDerivative t u)
        (forall u, m < u -> u <= X -> smoothedKernelDerivative t u <= 0)))) := by
  by_cases hEnd : 0 <= kernelTurnExpression t X
  case pos =>
    apply Exists.intro X
    apply And.intro hX
    apply And.intro le_rfl
    apply And.intro
    next =>
      intro u hu hum
      unfold smoothedKernelDerivative
      exact div_nonneg (kernelTurnExpression_nonneg_of_le t X u ht hu hum hEnd)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    next =>
      intro u hXu huX
      exfalso
      linarith
  case neg =>
    have htX : t <= X := by
      by_contra hh
      have hXt : X <= t := (lt_of_not_ge hh).le
      exact hEnd (kernelTurnExpression_nonneg_of_le t t X ht hX hXt
        (kernelTurnExpression_at_self_pos t ht).le)
    have hcont : ContinuousOn (kernelTurnExpression t) (Set.Icc t X) := by
      intro u hu
      exact (kernelTurnExpression_hasDerivAt t u
        (by have hh := hu.1; linarith)).continuousAt.continuousWithinAt
    have himage := intermediate_value_Icc' htX hcont
      (show Set.Icc (kernelTurnExpression t X) (kernelTurnExpression t t) 0 from
        And.intro (le_of_lt (lt_of_not_ge hEnd)) (kernelTurnExpression_at_self_pos t ht).le)
    cases himage with
    | intro m hm =>
      apply Exists.intro m
      apply And.intro (le_trans (show (1000 : Real) <= t by linarith) hm.1.1)
      apply And.intro hm.1.2
      apply And.intro
      next =>
        intro u hu hum
        unfold smoothedKernelDerivative
        exact div_nonneg (kernelTurnExpression_nonneg_of_le t m u ht hu hum
          (by rw [hm.2])) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      next =>
        intro u hmu huX
        have hg := kernelTurnExpression_antitone t ht hm.1.1
          (hm.1.1.trans hmu.le) hmu.le
        rw [hm.2] at hg
        unfold smoothedKernelDerivative
        exact div_nonpos_of_nonpos_of_nonneg hg (mul_nonneg (sq_nonneg _) (sq_nonneg _))

end Mertens
