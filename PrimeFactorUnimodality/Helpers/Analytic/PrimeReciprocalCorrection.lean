/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeFactorUnimodality.Helpers.Analytic.SharpMertensWeighted

/-!
# The prime reciprocal correction

The convergent sum of 1/(p(p-1)) over primes is below 81/100. The
nine primes below 24 are handled exactly; an integral bounds the full tail.
-/

set_option autoImplicit false

namespace Mertens

open Real Finset Filter Topology MeasureTheory

noncomputable def primeReciprocalCorrection : Real :=
  tsum (fun p : Nat => if p.Prime then 1 / ((p : Real) * ((p : Real) - 1)) else 0)

private theorem correction_summand_nonneg (p : Nat) :
    0 <= if p.Prime then 1 / ((p : Real) * ((p : Real) - 1)) else 0 := by
  split_ifs with hp
  case pos =>
    have hp1 : (1 : Real) <= p := by exact_mod_cast hp.one_le
    exact div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg p) (by linarith))
  case neg => rfl

theorem primeReciprocalCorrection_summable :
    Summable (fun p : Nat => if p.Prime then 1 / ((p : Real) * ((p : Real) - 1)) else 0) := by
  apply (primePowerLogTail_summable.mul_left (2 : Real)).of_nonneg_of_le
    correction_summand_nonneg
  intro p
  by_cases hp : p.Prime
  case pos =>
    simp only [if_pos hp]
    have hp2 : (2 : Real) <= p := by exact_mod_cast hp.two_le
    have hlog : 1 <= 2 * log (p : Real) := by
      have hl := log_le_log (by norm_num : (0 : Real) < 2) hp2
      linarith [LogTables.log_2_gt]
    have hden : 0 <= (p : Real) * ((p : Real) - 1) :=
      mul_nonneg (Nat.cast_nonneg p) (by linarith)
    have h := div_le_div_of_nonneg_right hlog hden
    convert h using 1 <;> ring
  case neg => simp [hp]

private noncomputable def correctionMajorant (t : Real) : Real := 1 / (t + 23) ^ 2

private theorem correctionMajorant_antitone :
    AntitoneOn correctionMajorant (Set.Ici 0) := by
  intro u hu v hv huv
  unfold correctionMajorant
  have hu0 : 0 <= u := hu
  have hv0 : 0 <= v := hv
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

private theorem correctionMajorant_deriv (x : Real) (hx : 0 <= x) :
    HasDerivAt (fun t => -1 / (t + 23)) (correctionMajorant x) x := by
  unfold correctionMajorant
  convert! HasDerivAt.fun_div (hasDerivAt_const x (-1))
    ((hasDerivAt_id' x).add_const 23) (by linarith : Not (x + 23 = 0)) using 1
  field_simp <;> ring

private theorem correctionMajorant_nonneg (t : Real) (ht : 0 < t) :
    0 <= correctionMajorant t := by
  unfold correctionMajorant
  positivity

private theorem correctionMajorant_limit :
    Tendsto (fun t : Real => -1 / (t + 23)) atTop (nhds 0) := by
  have h := (tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (23 : Real) tendsto_id)).neg
  simpa [div_eq_mul_inv, Function.comp_def] using h

private theorem correctionMajorant_integrable :
    IntegrableOn correctionMajorant (Set.Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' correctionMajorant_deriv
    correctionMajorant_nonneg correctionMajorant_limit

private theorem correctionMajorant_integral :
    MeasureTheory.integral (volume.restrict (Set.Ioi (0 : Real))) correctionMajorant = 1 / 23 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' correctionMajorant_deriv
    correctionMajorant_nonneg correctionMajorant_limit]
  norm_num

private theorem correctionMajorant_summable :
    Summable (fun n : Nat => correctionMajorant ((n : Real) + 1)) := by
  have h := correctionMajorant_antitone.summable_of_integrableOn_Ioi_zero
    correctionMajorant_integrable correctionMajorant_nonneg
  simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h

private theorem correctionMajorant_sum_le :
    tsum (fun n : Nat => correctionMajorant ((n : Real) + 1)) <= (1 : Real) / 23 := by
  have h := correctionMajorant_antitone.tsum_add_one_le_integral
    correctionMajorant_integrable correctionMajorant_nonneg
  simpa only [Nat.cast_add, Nat.cast_one, correctionMajorant_integral] using h

theorem primeReciprocalCorrection_lt_081 : primeReciprocalCorrection < (81 : Real) / 100 := by
  let f : Nat -> Real := fun p =>
    if p.Prime then 1 / ((p : Real) * ((p : Real) - 1)) else 0
  have hs : Summable f := primeReciprocalCorrection_summable
  have hfinite : (Finset.range 24).sum f + (24 : Real) / 529 < 81 / 100 := by
    norm_num [f, Finset.sum_range_succ]
  have hmajor (n : Nat) : f (n + 24) <=
      (24 : Real) / 23 * correctionMajorant ((n : Real) + 1) := by
    dsimp only [f, correctionMajorant]
    push_cast
    have hn : (0 : Real) <= n := by positivity
    split_ifs with hp
    case pos =>
      have hden : 23 * ((n : Real) + 24) / 24 <= (n : Real) + 24 - 1 := by linarith
      calc
        1 / (((n : Real) + 24) * ((n : Real) + 24 - 1)) <=
            1 / (((n : Real) + 24) * (23 * ((n : Real) + 24) / 24)) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (mul_le_mul_of_nonneg_left hden (by positivity))
        _ = (24 : Real) / 23 * (1 / ((n : Real) + 1 + 23) ^ 2) := by
          rw [show (n : Real) + 1 + 23 = n + 24 by ring]
          field_simp
    case neg => positivity
  have htail := ((summable_nat_add_iff 24).mpr hs).tsum_le_tsum hmajor
    (correctionMajorant_summable.mul_left ((24 : Real) / 23))
  rw [tsum_mul_left] at htail
  have htail' := htail.trans (mul_le_mul_of_nonneg_left correctionMajorant_sum_le
    (show (0 : Real) <= 24 / 23 by norm_num))
  have heq : primeReciprocalCorrection =
      (Finset.range 24).sum f + tsum (fun n : Nat => f (n + 24)) :=
    (hs.sum_add_tsum_nat_add 24).symm
  rw [heq]
  linarith

end Mertens
