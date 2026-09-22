import PrimeFactorUnimodality.Helpers.Analytic.XiHeightTail
import PrimeFactorUnimodality.Helpers.Analytic.XiLowReciprocalMass
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiDivisorPairing
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson.Reciprocal

/-! # An unconditional height-zero tail bound from finite reciprocal mass

Pair across the critical line and bound the inverse-height square by the
real reciprocal pair. The complete reciprocal mass is known exactly from
the functional equation and Hadamard constant. Subtracting the finite
low-height mass therefore gives an explicit bound for the actual tail.
Only a finite lower bound remains to certify a numerical tail constant;
no RH-dependent evaluation or assumed inverse-height total is imported.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real
open scoped ComplexConjugate

/-- The real reciprocal reflected pair is precisely the paired Poisson kernel at one. -/
theorem re_reciprocal_pair_eq_stechkinPair (ρ : ℂ) :
    (1 / ρ).re + (1 / (1 - conj ρ)).re = Real.stechkinPair 1 ρ.re ρ.im := by
  simp only [one_div, inv_re, normSq_apply, sub_re, one_re, conj_re, sub_im, one_im,
    conj_im, zero_sub, neg_neg, Real.stechkinPair, sub_self, zero_add]
  ring

/-- Exact mass subtraction bounds the full height-zero tail, without placing zeros on a line. -/
theorem xiHeightTail_zero_le_reciprocal_mass {H : ℝ} (hH : 0 < H) :
    xiHeightTail 0 H ≤ 2 * (1 + 1 / H ^ 2) *
      ((2 + Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 - xiLowReciprocalMass H) := by
  let P (ρ : ℂ) := H ≤ |ρ.im|
  let Q (ρ : ℂ) := (1 / ρ).re
  have hs : Summable (fun p : RiemannXiDivisorZeroIndex => Q (riemannXiDivisorZeroValue p)) :=
    summable_re_xi_divisor_reciprocal
  have href : Summable (fun p : RiemannXiDivisorZeroIndex =>
      Q (1 - conj (riemannXiDivisorZeroValue p))) :=
    (hs.comp_injective riemannXiDivisorSameHeightReflection.injective).congr
      (fun p => congrArg Q (riemannXiDivisorZeroValue_sameHeightReflection p))
  have hpair := (hs.add href).subtype (fun p => P (riemannXiDivisorZeroValue p))
  have hh := summable_xiHeightTail hH 0
  rw [abs_zero, zero_add] at hh
  simp only [zero_sub, neg_sq] at hh
  have hb := Summable.tsum_le_tsum
    (fun p : {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)} => show
      1 / (riemannXiDivisorZeroValue p.1).im ^ 2 ≤ (1 + 1 / H ^ 2) *
        (Q (riemannXiDivisorZeroValue p.1) + Q (1 - conj (riemannXiDivisorZeroValue p.1))) from by
      obtain ⟨hβ₀, hβ₁⟩ := riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p.1)
      have hy : H ^ 2 ≤ (riemannXiDivisorZeroValue p.1).im ^ 2 := by
        have h := (sq_le_sq₀ hH.le (abs_nonneg _)).mpr p.2
        simpa only [sq_abs] using h
      rw [show Q (riemannXiDivisorZeroValue p.1) +
          Q (1 - conj (riemannXiDivisorZeroValue p.1)) =
          Real.stechkinPair 1 (riemannXiDivisorZeroValue p.1).re
            (riemannXiDivisorZeroValue p.1).im from re_reciprocal_pair_eq_stechkinPair _]
      exact Real.inv_sq_le_stechkinPair_one hβ₀ hβ₁ hH hy)
    hh (hpair.mul_left (1 + 1 / H ^ 2))
  rw [tsum_mul_left] at hb
  have he := tsum_xi_divisor_subtype_eq_half_pair (G := Q) P (fun _ => by simp [P]) hs
  have hmass := tsum_xi_reciprocal_height_tail_eq H
  change (∑' p : {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)},
    Q (riemannXiDivisorZeroValue p.1)) = _ at hmass
  rw [hmass] at he
  unfold xiHeightTail
  rw [abs_zero, zero_add]
  simp only [zero_sub, neg_sq]
  nlinarith only [hb, congrArg (fun x => (1 + 1 / H ^ 2) * x) he]

/-- A finite collection of verified divisor labels supplies a numerical tail interface. -/
theorem xiHeightTail_zero_le_of_finite_mass {H B : ℝ} (hH : 0 < H)
    (S : Finset RiemannXiDivisorZeroIndex)
    (hS : ∀ p ∈ S, |(riemannXiDivisorZeroValue p).im| < H)
    (hB : B ≤ ∑ p ∈ S, (1 / riemannXiDivisorZeroValue p).re) :
    xiHeightTail 0 H ≤ 2 * (1 + 1 / H ^ 2) *
      ((2 + Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 - B) := by
  apply (xiHeightTail_zero_le_reciprocal_mass hH).trans
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_left (hB.trans (sum_reciprocal_le_xiLowReciprocalMass H S hS)) _)
    (by positivity)

end

end PrimeFactorUnimodality
