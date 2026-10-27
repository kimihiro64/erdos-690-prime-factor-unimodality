/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.NormNum.Prime
import PrimeFactorUnimodality.Helpers.Analytic.SharpThetaBounds
import VendorPrimeNumberTheoremAnd.Mertens

/-!
# An elementary uniform error bound for weighted reciprocal primes

Factorial bounds and the finite prime-power correction prove that the sum
of log(p)/p differs from log(x) by a number strictly between -2 and 1/5
for every real x >= 1000. The infinite correction tail is bounded by an
integral, using only the six primes through 13 separately.
-/

set_option autoImplicit false

namespace Mertens

open Real Finset Filter Topology MeasureTheory

noncomputable def primePowerLogTail : Real :=
  tsum (fun p : Nat => if p.Prime then log p / ((p : Real) * ((p : Real) - 1)) else 0)

private theorem primePowerLogTail_summand_nonneg (p : Nat) :
    0 <= if p.Prime then log p / ((p : Real) * ((p : Real) - 1)) else 0 := by
  split_ifs with hp
  case pos =>
    have hp1 : (1 : Real) <= p := by exact_mod_cast hp.one_le
    exact div_nonneg (log_natCast_nonneg p) (mul_nonneg (Nat.cast_nonneg p) (by linarith))
  case neg => rfl

theorem primePowerLogTail_summable :
    Summable (fun p : Nat => if p.Prime then log p / ((p : Real) * ((p : Real) - 1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr
    (by norm_num : 1 < (3 : Real) / 2) |>.const_div 4).of_nonneg_of_le
      primePowerLogTail_summand_nonneg ?_
  intro n
  split_ifs with hp
  case pos =>
    grw [Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : 0 < (1 : Real) / 2)]
    next =>
      have hden : (n : Real) * ((n : Real) - 1) >= (n : Real) ^ 2 / 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        have hn : (2 : Real) <= n := by exact_mod_cast hp.two_le
        linarith
      grw [hden]
      next =>
        apply le_of_eq
        rw [<- Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, <- Real.rpow_sub (by exact_mod_cast hp.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg n)]
        field
      next =>
        exact div_pos (pow_pos (by exact_mod_cast hp.pos) 2) (by norm_num)
    next =>
      apply mul_nonneg (Nat.cast_nonneg n)
      have hn : (1 : Real) <= n := by exact_mod_cast hp.one_le
      linarith
  case neg => positivity

theorem mangoldtLogSum_le_primeLogSum_add_tail (x : Real) (hx : 1 <= x) :
    (Finset.Ioc 0 (Nat.floor x)).sum
        (fun d => ArithmeticFunction.vonMangoldt d / (d : Real)) <=
      ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).sum
        (fun p => log p / (p : Real)) + primePowerLogTail := by
  simp_rw [ArithmeticFunction.vonMangoldt_apply, ite_div, zero_div, <- sum_filter,
    Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
    _ = (Finset.Icc 1 (Nat.floor (log x / log 2))).sum (fun k =>
        ((Finset.Ioc 0 (Nat.floor (x ^ (1 / (k : Real))))).filter Nat.Prime).sum
          (fun p => log p / ((p ^ k : Nat) : Real))) := by
      refine sum_congr rfl (fun k hk => sum_congr rfl (fun p hp => ?_))
      rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
    _ <= (Finset.Icc 1 (Nat.floor (log x / log 2))).sum (fun k =>
        ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).sum
          (fun p => log p / ((p ^ k : Nat) : Real))) := by
      gcongr with k hk
      apply rpow_le_self_of_one_le hx
      have hk1 : (1 : Real) <= k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have heq : (1 / (k : Real)) * k = 1 := by field_simp
      exact le_of_mul_le_mul_right (by rw [heq, one_mul]; exact hk1) (by linarith)
    _ <= (Finset.Icc 1 (max 1 (Nat.floor (log x / log 2)))).sum (fun k =>
        ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).sum
          (fun p => log p / ((p ^ k : Nat) : Real))) := by
      apply sum_le_sum_of_subset_of_nonneg
      next => gcongr; exact le_max_right 1 (Nat.floor (log x / log 2))
      next => intros; exact sum_nonneg (by intros; positivity)
    _ = ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).sum (fun p => log p / (p : Real)) +
        (Finset.Ioc 1 (max 1 (Nat.floor (log x / log 2)))).sum (fun k =>
          ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).sum
            (fun p => log p / ((p ^ k : Nat) : Real))) := by
      rw [<- add_sum_Ioc_eq_sum_Icc (le_max_left 1 (Nat.floor (log x / log 2)))]
      simp
    _ <= _ := by
      gcongr
      rw [sum_comm]
      conv =>
        lhs; arg 2; ext p; arg 2; ext k
        rw [<- mul_one_div, Nat.cast_pow, <- one_div_pow]
      simp_rw [<- mul_sum]
      calc
        _ <= ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).sum
            (fun p => log p / ((p : Real) * ((p : Real) - 1))) := by
          gcongr with p hp
          simp only [mem_filter, mem_Ioc] at hp
          conv => rhs; rw [<- mul_one_div]
          gcongr
          rw [show Finset.Ioc 1 (max 1 (Nat.floor (log x / log 2))) =
            Finset.Ico 2 (max 1 (Nat.floor (log x / log 2)) + 1) from rfl]
          grw [geom_sum_Ico_le_of_lt_one (by simp)]
          next =>
            apply le_of_eq
            have hp0 : Not ((p : Real) = 0) := by exact_mod_cast hp.2.ne_zero
            field
          next =>
            have hp1 : (1 : Real) < p := by exact_mod_cast hp.2.one_lt
            have heq : (1 / (p : Real)) * p = 1 := by field_simp
            by_contra h
            have hh : 1 <= 1 / (p : Real) := le_of_not_gt h
            have hm := mul_le_mul_of_nonneg_right hh (show (0 : Real) <= p by positivity)
            rw [heq, one_mul] at hm
            linarith
        _ <= primePowerLogTail := by
          rw [sum_filter]
          exact primePowerLogTail_summable.sum_le_tsum _
            (fun p _ => primePowerLogTail_summand_nonneg p)

private noncomputable def logSquareTail (t : Real) : Real := log (t + 16) / (t + 16) ^ 2

private theorem logSquareTail_antitone :
    AntitoneOn logSquareTail (Set.Ici 0) := by
  unfold logSquareTail
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  next =>
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have hn : Not (t + 16 = 0) := by simp only [Set.mem_Ici] at ht; linarith
    fun_prop (disch := grind)
  next =>
    intro t ht
    apply DifferentiableAt.differentiableWithinAt
    have hn : Not ((t + 16) ^ 2 = 0) := by
      apply pow_ne_zero
      simp at ht
      linarith
    fun_prop (disch := grind)
  next =>
    intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop)
      (by positivity), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    have hl : 1 <= log (t + 16) :=
      (le_log_iff_exp_le (by linarith)).mpr (by linarith [exp_one_lt_three])
    linarith

private theorem logSquareTail_nonneg :
    forall t, 0 < t -> 0 <= logSquareTail t := by
  intro t ht
  have htpos : 0 < t := ht
  exact div_nonneg (log_nonneg (by linarith)) (by positivity)

private theorem logSquareTail_deriv :
    forall x, 0 <= x ->
      HasDerivAt (fun t => (-log (t + 16) - 1) / (t + 16)) (logSquareTail x) x := by
  intro t ht
  have htpos : 0 <= t := ht
  unfold logSquareTail
  apply HasDerivAt.comp_add_const (f := (fun t => (-log t - 1) / t)) t 16
  convert! HasDerivAt.fun_div (c' := -1 / (t + 16)) (d' := (1 : Real)) ?_ ?_ ?_ using 1
  next => field
  next =>
    apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by linarith : Not (t + 16 = 0))).neg using 1 <;> ring
  next => exact hasDerivAt_id (t + 16)
  next => linarith

private theorem logSquareTail_antideriv_tendsto :
    Tendsto (fun t : Real => (-log (t + 16) - 1) / (t + 16)) atTop (nhds 0) := by
  have hshift : Tendsto (fun t : Real => t + 16) atTop atTop :=
    tendsto_atTop_add_const_right atTop 16 tendsto_id
  apply Tendsto.comp (g := (fun t : Real => (-log t - 1) / t)) ?_ hshift
  convert! Tendsto.sub (f := (fun t : Real => -log t / t)) (a := 0)
    ?_ tendsto_inv_atTop_zero using 1
  next => ring_nf
  next => ring_nf
  next =>
    convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    next => ext t; ring
    next => simp

private theorem logSquareTail_integrable :
    IntegrableOn logSquareTail (Set.Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' logSquareTail_deriv
    logSquareTail_nonneg logSquareTail_antideriv_tendsto

private theorem logSquareTail_integral :
    (MeasureTheory.integral (volume.restrict (Set.Ioi (0 : Real))) logSquareTail) =
      (log 16 + 1) / 16 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' logSquareTail_deriv
    logSquareTail_nonneg logSquareTail_antideriv_tendsto]
  ring_nf

private theorem logSquareTail_summable :
    Summable (fun n : Nat => logSquareTail ((n : Real) + 1)) := by
  have h := logSquareTail_antitone.summable_of_integrableOn_Ioi_zero
    logSquareTail_integrable logSquareTail_nonneg
  simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h

private theorem logSquareTail_sum_le :
    tsum (fun n : Nat => logSquareTail ((n : Real) + 1)) <= (log 16 + 1) / 16 := by
  have h := logSquareTail_antitone.tsum_add_one_le_integral
    logSquareTail_integrable logSquareTail_nonneg
  simpa only [Nat.cast_add, Nat.cast_one] using h.trans_eq logSquareTail_integral

theorem primePowerLogTail_lt_098 : primePowerLogTail < (98 : Real) / 100 := by
  let f : Nat -> Real := fun p =>
    if p.Prime then log p / ((p : Real) * ((p : Real) - 1)) else 0
  have hs : Summable f := primePowerLogTail_summable
  have hfinite : (Finset.range 17).sum f < (7 : Real) / 10 := by
    norm_num [f, Finset.sum_range_succ]
    linarith [LogTables.log_2_lt, LogTables.log_3_lt, LogTables.log_5_lt,
      LogTables.log_7_lt, LogTables.log_11_lt, LogTables.log_13_lt]
  have hmajor (n : Nat) : f (n + 17) <=
      (17 : Real) / 16 * logSquareTail ((n : Real) + 1) := by
    dsimp only [f, logSquareTail]
    push_cast
    have hn : (0 : Real) <= n := by positivity
    split_ifs with hp
    case pos =>
      have hlog : 0 <= log ((n : Real) + 17) := log_nonneg (by linarith)
      have hden : 16 * ((n : Real) + 17) / 17 <= (n : Real) + 17 - 1 := by linarith
      calc
        log ((n : Real) + 17) / (((n : Real) + 17) * ((n : Real) + 17 - 1)) <=
            log ((n : Real) + 17) /
              (((n : Real) + 17) * (16 * ((n : Real) + 17) / 17)) :=
          div_le_div_of_nonneg_left hlog (by positivity)
            (mul_le_mul_of_nonneg_left hden (by positivity))
        _ = (17 : Real) / 16 * (log ((n : Real) + 1 + 16) /
            ((n : Real) + 1 + 16) ^ 2) := by
          rw [show (n : Real) + 1 + 16 = n + 17 by ring]
          field_simp <;> ring
    case neg =>
      apply mul_nonneg (by norm_num)
      apply div_nonneg (log_nonneg (by linarith)) (by positivity)
  have htail := ((summable_nat_add_iff 17).mpr hs).tsum_le_tsum hmajor
    (logSquareTail_summable.mul_left ((17 : Real) / 16))
  rw [tsum_mul_left] at htail
  have htail' := htail.trans (mul_le_mul_of_nonneg_left logSquareTail_sum_le
    (show (0 : Real) <= 17 / 16 by norm_num))
  have heq : primePowerLogTail =
      (Finset.range 17).sum f + tsum (fun n : Nat => f (n + 17)) := by
    exact (hs.sum_add_tsum_nat_add 17).symm
  have hlog16 : log (16 : Real) < 28 / 10 := by
    rw [show (16 : Real) = 2 ^ (4 : Nat) by norm_num, log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [LogTables.log_2_lt]
  rw [heq]
  linarith


noncomputable def primeLogSum (x : Real) : Real :=
  ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).sum (fun p => log p / (p : Real))

noncomputable def mangoldtLogSum (x : Real) : Real :=
  (Finset.Ioc 0 (Nat.floor x)).sum
    (fun d => ArithmeticFunction.vonMangoldt d / (d : Real))

noncomputable def primeLogError (x : Real) : Real := primeLogSum x - log x

theorem primeLogSum_le_mangoldtLogSum (x : Real) :
    primeLogSum x <= mangoldtLogSum x := by
  unfold primeLogSum mangoldtLogSum
  rw [sum_filter]
  apply sum_le_sum
  intro p hp
  split_ifs with hprime
  case pos => rw [ArithmeticFunction.vonMangoldt_apply_prime hprime]
  case neg => positivity

theorem factorial_mangoldt_sandwich (x : Real) (hx : 0 <= x) :
    And (log ((Nat.floor x).factorial) <= x * mangoldtLogSum x)
      (x * mangoldtLogSum x <= log ((Nat.floor x).factorial) + Chebyshev.psi x) := by
  have hfac : log ((Nat.floor x).factorial) =
      (Finset.Ioc 0 (Nat.floor x)).sum
        (fun d => ArithmeticFunction.vonMangoldt d * (Nat.floor (x / d) : Real)) := by
    rw [<- sum_log_eq_log_factorial, sum_log_eq_sum_mangoldt]
  apply And.intro
  next =>
    rw [hfac, mangoldtLogSum, Finset.mul_sum]
    apply sum_le_sum
    intro d hd
    have hm := mul_le_mul_of_nonneg_left
      (Nat.floor_le (div_nonneg hx (Nat.cast_nonneg d)))
      (ArithmeticFunction.vonMangoldt_nonneg (n := d))
    convert hm using 1 <;> ring
  next =>
    calc
      x * mangoldtLogSum x =
          (Finset.Ioc 0 (Nat.floor x)).sum
            (fun d => ArithmeticFunction.vonMangoldt d * (x / d)) := by
        unfold mangoldtLogSum
        rw [Finset.mul_sum]
        congr 1
        funext d
        ring
      _ <= (Finset.Ioc 0 (Nat.floor x)).sum
          (fun d => ArithmeticFunction.vonMangoldt d * ((Nat.floor (x / d) : Real) + 1)) := by
        apply sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one (x / d)).le
          (ArithmeticFunction.vonMangoldt_nonneg (n := d))
      _ = log ((Nat.floor x).factorial) + Chebyshev.psi x := by
        simp_rw [mul_add, mul_one]
        rw [sum_add_distrib, <- hfac]
        rfl

theorem primeLogError_bounds (x : Real) (hx : 1000 <= x) :
    And (-2 < primeLogError x) (primeLogError x < (1 : Real) / 5) := by
  have hxpos : 0 < x := by linarith
  have hfloor := factorial_mangoldt_sandwich x hxpos.le
  have hfact := Real.log_factorial_floor_half_bounds x (by linarith)
  have hpsi := Chebyshev.psi_upper_116_from_1000 x hx
  have hlog := Chebyshev.log_le_seven_thousandths_mul x hx
  have htail := mangoldtLogSum_le_primeLogSum_add_tail x (by linarith)
  change mangoldtLogSum x <= primeLogSum x + primePowerLogTail at htail
  have htailScaled := mul_le_mul_of_nonneg_left htail hxpos.le
  have hD := mul_lt_mul_of_pos_left primePowerLogTail_lt_098 hxpos
  have hB := mul_le_mul_of_nonneg_left (primeLogSum_le_mangoldtLogSum x) hxpos.le
  unfold primeLogError
  apply And.intro
  next =>
    by_contra h
    have hh : primeLogSum x - log x <= -2 := le_of_not_gt h
    have hm := mul_le_mul_of_nonneg_left hh hxpos.le
    nlinarith only [hfloor.1, hfact.1, htailScaled, hD, hm, hlog, hx]
  next =>
    by_contra h
    have hh : (1 : Real) / 5 <= primeLogSum x - log x := le_of_not_gt h
    have hm := mul_le_mul_of_nonneg_left hh hxpos.le
    nlinarith only [hfloor.2, hfact.2, hpsi, hB, hm, hlog, hx]
end Mertens
