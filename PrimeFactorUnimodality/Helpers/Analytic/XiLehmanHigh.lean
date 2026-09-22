import PrimeFactorUnimodality.Helpers.Analytic.BacklundCountingHigh
import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanRemainder

/-! # The proved numerical counting envelope in the high Lehman tail

The high-height counting estimate now supplies the discrepancy hypothesis
of the existing infinite Abel identity. A deliberately simple cutoff of
`10^9` suffices; all positive harmonic heights used with `T0=3.06*10^10`
lie above it. The strict count's left limit absorbs the exact cutoff
multiplicity, so no unproved nonvanishing assumption or boundary-mass term
remains. Numerical low-zero and separation inputs remain separate.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real Set MeasureTheory

/-- An elementary exponential comparison verifies the high-height threshold. -/
theorem seventeen_le_log_of_billion_le {T : ℝ} (hT : 10 ^ 9 ≤ T) :
    17 ≤ Real.log T := by
  apply (Real.le_log_iff_exp_le (by linarith : 0 < T)).mpr
  have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 17
  rw [← Real.exp_nat_mul] at he
  norm_num at he
  linarith

/-- The actual multiplicity-counted discrepancy has the required numerical envelope. -/
theorem abs_xiZeroCountingRemainder_le_two_log_high {T : ℝ} (hT : 10 ^ 9 ≤ T) :
    |xiZeroCountingRemainder T| ≤ 2 * Real.log T :=
  abs_xiZeroCountingRemainder_le_two_log (by linarith) (seventeen_le_log_of_billion_le hT)

/-- The strict positive-ordinate pair sum has the unconditional Lehman error bound. -/
theorem abs_xi_strict_pair_tail_sub_main_le_high {t H : ℝ}
    (ht : 0 < t) (hH : 0 < H) (hA : 10 ^ 9 ≤ t + H) :
    |(∑' p : {p : RiemannXiDivisorZeroIndex // t + H < (riemannXiDivisorZeroValue p).im},
      Real.reciprocalSquarePair t (riemannXiDivisorZeroValue p.1).im) - xiLehmanMainIntegral t H| ≤
      xiLehmanIntegralCorrection t H :=
  abs_xi_strict_pair_tail_sub_main_le_of_counting_error ht hH
    (fun _ hx => abs_xiZeroCountingRemainder_le_two_log_high (hA.trans hx))

/-- The strict count has the same numerical envelope at every high cutoff. -/
theorem abs_xiStrictZeroCount_sub_mainTerm_le_two_log_high {T : ℝ} (hT : 10 ^ 9 ≤ T) :
    |(xiStrictZeroCount T : ℝ) - xiZeroCountingMainTerm T| ≤ 2 * Real.log T := by
  have h := abs_xiStrictZeroCount_sub_mainTerm_le_log_add (by linarith : 10 < T)
  linarith [seventeen_le_log_of_billion_le hT]

/-- The full closed tail satisfies the Lehman bound even when the cutoff is a zero ordinate. -/
theorem xiHeightTail_le_main_add_correction_high {t H : ℝ}
    (ht : 0 < t) (hH : 0 < H) (hA : 10 ^ 9 ≤ t + H) :
    xiHeightTail t H ≤ xiLehmanMainIntegral t H + xiLehmanIntegralCorrection t H := by
  have hRi := integrableOn_xiCountingRemainder_mul_slope ht hH
  have hLi : IntegrableOn (fun x => Real.log x * Real.reciprocalSquarePairSlope t x)
      (Ioi (t + H)) := by
    simpa only [sub_zero] using Real.integrableOn_log_sub_mul_reciprocalSquarePairSlope ht hH 0
  have hI : (∫ x in Ioi (t + H), xiZeroCountingRemainder x * Real.reciprocalSquarePairSlope t x) ≤
      2 * ∫ x in Ioi (t + H), Real.log x * Real.reciprocalSquarePairSlope t x := by
    rw [← integral_const_mul]
    apply integral_mono_ae hRi (hLi.const_mul 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : t + H < x := hx
    have hb := (le_abs_self (xiZeroCountingRemainder x)).trans
      (abs_xiZeroCountingRemainder_le_two_log_high (hA.trans hx'.le))
    have hxT : t < x := by linarith
    convert mul_le_mul_of_nonneg_right hb
      (Real.reciprocalSquarePairSlope_nonneg ht.le hxT) using 1
    ring
  have hφ : 0 ≤ Real.reciprocalSquarePair t (t + H) :=
    (Real.reciprocalSquarePair_pos ht.le (by linarith)).le
  have hB : -((xiStrictZeroCount (t + H) : ℝ) - xiZeroCountingMainTerm (t + H)) *
      Real.reciprocalSquarePair t (t + H) ≤
        2 * Real.log (t + H) * Real.reciprocalSquarePair t (t + H) :=
    mul_le_mul_of_nonneg_right ((neg_le_abs _).trans
      (abs_xiStrictZeroCount_sub_mainTerm_le_two_log_high hA)) hφ
  have hc : (xiZeroCount (t + H) : ℝ) = (xiStrictZeroCount (t + H) : ℝ) +
      (xiOrdinateMultiplicity (t + H) : ℝ) := by
    exact_mod_cast xiZeroCount_eq_strict_add_multiplicity (by linarith : 0 < t + H)
  have he : xiHeightTail t H - xiLehmanMainIntegral t H =
      -((xiStrictZeroCount (t + H) : ℝ) - xiZeroCountingMainTerm (t + H)) *
        Real.reciprocalSquarePair t (t + H) +
          ∫ x in Ioi (t + H), xiZeroCountingRemainder x * Real.reciprocalSquarePairSlope t x := by
    rw [xiHeightTail_sub_main_eq_error_add_boundary ht hH]
    conv_lhs => lhs; lhs; rw [xiZeroCountingRemainder, hc]
    ring
  have hc' : 2 * Real.log (t + H) * Real.reciprocalSquarePair t (t + H) +
      2 * (∫ x in Ioi (t + H), Real.log x * Real.reciprocalSquarePairSlope t x) =
        xiLehmanIntegralCorrection t H := by
    rw [Real.integral_log_mul_reciprocalSquarePairSlope ht hH]
    unfold xiLehmanIntegralCorrection
    rw [integral_Ioi_comp_add t H (fun x => Real.reciprocalSquarePair t x / x), add_comm H t]
    ring
  have h := add_le_add hB hI
  rw [← he, hc'] at h
  linarith

end

end PrimeFactorUnimodality
