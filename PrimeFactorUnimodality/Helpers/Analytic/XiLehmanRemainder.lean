import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanAbel
import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanSmoothTerm

/-! # Exact infinite counting discrepancy and the Lehman error estimate

Subtract the smooth counting term from the unconditional actual-zero
identity. The resulting error integral is genuinely integrable. The last
theorems derive the Lehman estimate from an explicit bound on the actual
counting discrepancy; proving that numerical bound remains a separate
obligation. All closed-cutoff multiplicities are retained.
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Real Set

/-- The actual counting discrepancy has an absolutely integrable pair-slope weight. -/
theorem integrableOn_xiCountingRemainder_mul_slope {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    IntegrableOn (fun x => xiZeroCountingRemainder x * Real.reciprocalSquarePairSlope t x)
      (Ioi (t + H)) := by
  have hN : IntegrableOn (fun x => (xiZeroCount x : ℝ) * Real.reciprocalSquarePairSlope t x)
      (Ioi (t + H)) := (xi_strict_pair_tail_eq_count_integral ht.le hH).1
  apply (hN.sub (integrableOn_xiCountingMain_mul_slope ht hH)).congr_fun _ measurableSet_Ioi
  intro x _
  simp only [Pi.sub_apply, xiZeroCountingRemainder, sub_mul]

/-- Exact error for the actual strict positive-ordinate tail, with no counting bound assumed. -/
theorem xi_strict_pair_tail_sub_main_eq_error {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // t + H < (riemannXiDivisorZeroValue p).im},
      Real.reciprocalSquarePair t (riemannXiDivisorZeroValue p.1).im) - xiLehmanMainIntegral t H =
      -xiZeroCountingRemainder (t + H) * Real.reciprocalSquarePair t (t + H) +
        ∫ x in Ioi (t + H), xiZeroCountingRemainder x * Real.reciprocalSquarePairSlope t x := by
  have hN : IntegrableOn (fun x => (xiZeroCount x : ℝ) * Real.reciprocalSquarePairSlope t x)
      (Ioi (t + H)) := (xi_strict_pair_tail_eq_count_integral ht.le hH).1
  have hR : (∫ x in Ioi (t + H), xiZeroCountingRemainder x * Real.reciprocalSquarePairSlope t x) =
      (∫ x in Ioi (t + H), (xiZeroCount x : ℝ) * Real.reciprocalSquarePairSlope t x) -
        ∫ x in Ioi (t + H), xiZeroCountingMainTerm x * Real.reciprocalSquarePairSlope t x := by
    simp only [xiZeroCountingRemainder, sub_mul]
    exact integral_sub hN (integrableOn_xiCountingMain_mul_slope ht hH)
  rw [hR, integral_xiCountingMain_mul_slope ht hH,
    (xi_strict_pair_tail_eq_count_integral ht.le hH).2]
  simp only [Real.reciprocalSquarePairSlope, xiZeroCountingRemainder]
  ring

/-- The closed height tail adds exactly the entire cutoff atom to the error identity. -/
theorem xiHeightTail_sub_main_eq_error_add_boundary {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    xiHeightTail t H - xiLehmanMainIntegral t H =
      -xiZeroCountingRemainder (t + H) * Real.reciprocalSquarePair t (t + H) +
        (∫ x in Ioi (t + H), xiZeroCountingRemainder x * Real.reciprocalSquarePairSlope t x) +
        (xiOrdinateMultiplicity (t + H) : ℝ) * Real.reciprocalSquarePair t (t + H) := by
  rw [xiHeightTail_eq_strict_positive_add_boundary hH, abs_of_nonneg ht.le]
  linarith [xi_strict_pair_tail_sub_main_eq_error ht hH]

/-- The actual counting-error bound implies the precise Lehman correction for the strict tail. -/
theorem abs_xi_strict_pair_tail_sub_main_le_of_counting_error {t H : ℝ}
    (ht : 0 < t) (hH : 0 < H)
    (hR : ∀ x ∈ Ici (t + H), |xiZeroCountingRemainder x| ≤ 2 * Real.log x) :
    |(∑' p : {p : RiemannXiDivisorZeroIndex // t + H < (riemannXiDivisorZeroValue p).im},
      Real.reciprocalSquarePair t (riemannXiDivisorZeroValue p.1).im) - xiLehmanMainIntegral t H| ≤
      xiLehmanIntegralCorrection t H := by
  have hRi := integrableOn_xiCountingRemainder_mul_slope ht hH
  have hLi : IntegrableOn (fun x => Real.log x * Real.reciprocalSquarePairSlope t x)
      (Ioi (t + H)) := by
    simpa only [sub_zero] using Real.integrableOn_log_sub_mul_reciprocalSquarePairSlope ht hH 0
  have hI : (∫ x in Ioi (t + H), |xiZeroCountingRemainder x * Real.reciprocalSquarePairSlope t x|) ≤
      2 * ∫ x in Ioi (t + H), Real.log x * Real.reciprocalSquarePairSlope t x := by
    rw [← integral_const_mul]
    apply integral_mono_ae hRi.abs (hLi.const_mul 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : t < x := by have : t + H < x := hx; linarith
    rw [abs_mul, abs_of_nonneg (Real.reciprocalSquarePairSlope_nonneg ht.le hx')]
    exact (mul_le_mul_of_nonneg_right (hR x (mem_Ici.mpr (mem_Ioi.mp hx).le))
      (Real.reciprocalSquarePairSlope_nonneg ht.le hx')).trans_eq (by ring)
  have hφ : 0 < Real.reciprocalSquarePair t (t + H) :=
    Real.reciprocalSquarePair_pos ht.le (by linarith)
  have hB : |-xiZeroCountingRemainder (t + H) * Real.reciprocalSquarePair t (t + H)| ≤
      2 * Real.log (t + H) * Real.reciprocalSquarePair t (t + H) := by
    rw [abs_mul, abs_neg, abs_of_pos hφ]
    exact mul_le_mul_of_nonneg_right (hR (t + H) (mem_Ici.mpr le_rfl)) hφ.le
  rw [xi_strict_pair_tail_sub_main_eq_error ht hH]
  have hE := (abs_add_le
    (-xiZeroCountingRemainder (t + H) * Real.reciprocalSquarePair t (t + H))
    (∫ x in Ioi (t + H), xiZeroCountingRemainder x * Real.reciprocalSquarePairSlope t x)).trans
      (add_le_add hB (abs_integral_le_integral_abs.trans hI))
  apply hE.trans_eq
  rw [Real.integral_log_mul_reciprocalSquarePairSlope ht hH]
  unfold xiLehmanIntegralCorrection
  rw [integral_Ioi_comp_add t H (fun x => Real.reciprocalSquarePair t x / x), add_comm H t]
  ring

/-- The closed tail inherits the Lehman estimate only with its exact boundary multiplicity. -/
theorem xiHeightTail_le_main_add_correction_of_counting_error {t H : ℝ}
    (ht : 0 < t) (hH : 0 < H)
    (hR : ∀ x ∈ Ici (t + H), |xiZeroCountingRemainder x| ≤ 2 * Real.log x) :
    xiHeightTail t H ≤ xiLehmanMainIntegral t H + xiLehmanIntegralCorrection t H +
      (xiOrdinateMultiplicity (t + H) : ℝ) * Real.reciprocalSquarePair t (t + H) := by
  have h := abs_xi_strict_pair_tail_sub_main_le_of_counting_error ht hH hR
  have hupper := (le_abs_self _).trans h
  rw [xiHeightTail_eq_strict_positive_add_boundary hH, abs_of_nonneg ht.le]
  linarith

end

end PrimeFactorUnimodality
