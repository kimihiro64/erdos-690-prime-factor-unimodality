/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeFactorUnimodality.Helpers.Analytic.SharpMertensWeighted

/-!
# Abel summation for weighted prime logarithms

The formula uses real endpoints and explicitly includes the prime at 2.
The reciprocal-prime specialization is the finite identity needed for the
sharp elementary Mertens error estimate.
-/

set_option autoImplicit false

namespace Mertens

open Real Finset MeasureTheory

noncomputable def primeLogCoefficient (p : Nat) : Real :=
  if p.Prime then log p / (p : Real) else 0

theorem primeLogSum_eq_sum_Icc (x : Real) :
    primeLogSum x = (Finset.Icc 0 (Nat.floor x)).sum primeLogCoefficient := by
  unfold primeLogSum
  rw [sum_filter, <- add_sum_Ioc_eq_sum_Icc (Nat.zero_le (Nat.floor x))]
  simp [primeLogCoefficient]

noncomputable def weightedPrimeLogSum (g : Real -> Real) (x : Real) : Real :=
  (Finset.Icc 0 (Nat.floor x)).sum (fun p => g p * primeLogCoefficient p)

theorem weightedPrimeLogSum_abel (g : Real -> Real) (x : Real) (hx : 2 <= x)
    (hd : forall t, Set.Icc 2 x t -> DifferentiableAt Real g t)
    (hi : IntegrableOn (deriv g) (Set.Icc 2 x)) :
    weightedPrimeLogSum g x = g x * primeLogSum x -
      MeasureTheory.integral (volume.restrict (Set.Ioc 2 x))
        (fun t => deriv g t * primeLogSum t) := by
  have hsub : Finset.Icc 0 2 <= Finset.Icc 0 (Nat.floor x) := by
    intro n hn
    have hn2 := (Finset.mem_Icc.mp hn).2
    have hfloor : 2 <= Nat.floor x := Nat.le_floor hx
    simp only [Finset.mem_Icc] at hn
    exact Finset.mem_Icc.mpr (And.intro (by omega) (by omega))
  have hdiff : Finset.Icc 0 (Nat.floor x) \ Finset.Icc 0 2 =
      Finset.Ioc 2 (Nat.floor x) := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsplit := Finset.sum_sdiff_eq_sub
    (f := fun p : Nat => g p * primeLogCoefficient p) hsub
  rw [hdiff] at hsplit
  have hsmall : (Finset.Icc (0 : Nat) 2).sum (fun p : Nat => g p * primeLogCoefficient p) =
      g 2 * primeLogCoefficient 2 := by
    norm_num [show Finset.Icc 0 2 = {0, 1, 2} by decide, primeLogCoefficient]
  rw [hsmall] at hsplit
  have hc2 : (Finset.Icc (0 : Nat) 2).sum primeLogCoefficient = primeLogCoefficient 2 := by
    norm_num [show Finset.Icc 0 2 = {0, 1, 2} by decide, primeLogCoefficient]
  have h := sum_mul_eq_sub_sub_integral_mul primeLogCoefficient (a := 2) (b := x)
    (by norm_num) hx hd hi
  rw [show Nat.floor (2 : Real) = 2 by norm_num, hsplit] at h
  simp_rw [<- primeLogSum_eq_sum_Icc] at h
  rw [hc2] at h
  unfold weightedPrimeLogSum
  linarith

noncomputable def primeReciprocalSum (x : Real) : Real :=
  (Finset.Icc 0 (Nat.floor x)).sum (fun p => if p.Prime then 1 / (p : Real) else 0)

theorem reciprocalPrimeSum_abel (x : Real) (hx : 2 <= x) :
    primeReciprocalSum x = primeLogSum x / log x +
      intervalIntegral (fun t => primeLogSum t / (t * log t ^ 2)) 2 x volume := by
  let g : Real -> Real := fun t => Inv.inv (log t)
  have hd : forall t, Set.Icc 2 x t -> DifferentiableAt Real g t := by
    intro t ht
    have htpos : 0 < t := by have hh := ht.1; linarith
    have htlog : Not (log t = 0) := ne_of_gt (log_pos (by have hh := ht.1; linarith))
    dsimp only [g]
    fun_prop
  have hderiv : deriv g = fun t => -(1 / (t * log t ^ 2)) := by
    funext t
    dsimp only [g]
    rw [deriv_inv_log]
    simp only [one_div, div_eq_mul_inv]
    ring
  have hi : IntegrableOn (deriv g) (Set.Icc 2 x) := by
    rw [hderiv]
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have htpos : 0 < t := by have hh := ht.1; linarith
    have htlog : Not (log t = 0) := ne_of_gt (log_pos (by have hh := ht.1; linarith))
    fun_prop (disch := grind)
  have hs : weightedPrimeLogSum g x = primeReciprocalSum x := by
    unfold weightedPrimeLogSum primeReciprocalSum
    apply sum_congr rfl
    intro p hp
    unfold primeLogCoefficient
    split_ifs with hprime
    case pos =>
      have hp0 : Not ((p : Real) = 0) := by exact_mod_cast hprime.ne_zero
      have hlog : Not (log (p : Real) = 0) := ne_of_gt (log_pos (by exact_mod_cast hprime.one_lt))
      dsimp only [g]
      field_simp
    case neg => ring
  have h := weightedPrimeLogSum_abel g x hx hd hi
  rw [hs, hderiv] at h
  have heq : MeasureTheory.integral (volume.restrict (Set.Ioc 2 x))
      (fun t => -(1 / (t * log t ^ 2)) * primeLogSum t) =
      -intervalIntegral (fun t => primeLogSum t / (t * log t ^ 2)) 2 x volume := by
    rw [intervalIntegral.integral_of_le hx, <- integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    ring
  rw [heq] at h
  dsimp only [g] at h
  convert h using 1 <;> ring

end Mertens
