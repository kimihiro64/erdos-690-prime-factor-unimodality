import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanMainIntegral
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingRemainder
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePairWeighted

/-! # Removing the smooth counting term from the infinite tail

The smooth counting function and its derivative are integrated against the
actual pair kernel. All improper integrals are proved integrable, and the
upper boundary is proved to vanish. The resulting identity recovers the
previously evaluated main integral exactly.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

/-- The untranslated logarithmic density is genuinely integrable. -/
theorem integrableOn_xiLehmanDensity {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    IntegrableOn (fun x => ((1 / (2 * π)) * Real.log (x / (2 * π))) *
      Real.reciprocalSquarePair t x) (Ioi (t + H)) := by
  rw [add_comm t H, ← integrableOn_Ioi_comp_add_iff t H]
  simpa only [IntegrableOn, mul_assoc] using
    (integrableOn_xiLehmanMainIntegrand ht hH).const_mul (1 / (2 * π))

/-- Translation identifies the unshifted density integral with the already-evaluated main term. -/
theorem integral_xiLehmanDensity_eq (t H : ℝ) :
    (∫ x in Ioi (t + H), ((1 / (2 * π)) * Real.log (x / (2 * π))) *
      Real.reciprocalSquarePair t x) = xiLehmanMainIntegral t H := by
  rw [add_comm t H, ← integral_Ioi_comp_add t H]
  simp only [mul_assoc, integral_const_mul, xiLehmanMainIntegral]

/-- The smooth counting term times the negative derivative of the pair is integrable. -/
theorem integrableOn_xiCountingMain_mul_slope {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    IntegrableOn (fun x => xiZeroCountingMainTerm x * Real.reciprocalSquarePairSlope t x)
      (Ioi (t + H)) := by
  have h := Real.integrableOn_mul_log_sub_mul_reciprocalSquarePairSlope ht hH
    (Real.log (2 * π) + 1)
  apply IntegrableOn.congr_fun (h.const_mul (1 / (2 * π))) _ measurableSet_Ioi
  intro x hx
  have hxpos : 0 < x := by have : t + H < x := hx; linarith
  dsimp only [xiZeroCountingMainTerm]
  rw [Real.log_div hxpos.ne' (by positivity : 2 * π ≠ 0)]
  ring

/-- The upper smooth-counting boundary vanishes without any information about zero counts. -/
theorem tendsto_xiCountingMain_mul_pair (t : ℝ) :
    Tendsto (fun x => xiZeroCountingMainTerm x * Real.reciprocalSquarePair t x) atTop (𝓝 0) := by
  have h := (Real.tendsto_mul_log_sub_mul_reciprocalSquarePair_atTop t
    (Real.log (2 * π) + 1)).const_mul (1 / (2 * π))
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa only [mul_zero] using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [xiZeroCountingMainTerm]
  rw [Real.log_div hx.ne' (by positivity : 2 * π ≠ 0)]
  ring

/-- Integration by parts recovers the smooth logarithmic main integral and its lower boundary. -/
theorem integral_xiCountingMain_mul_slope {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    (∫ x in Ioi (t + H), xiZeroCountingMainTerm x * Real.reciprocalSquarePairSlope t x) =
      xiLehmanMainIntegral t H +
        xiZeroCountingMainTerm (t + H) * Real.reciprocalSquarePair t (t + H) := by
  have hd (x : ℝ) (hx : x ∈ Ici (t + H)) :
      HasDerivAt (fun y => xiZeroCountingMainTerm y * Real.reciprocalSquarePair t y)
        (((1 / (2 * π)) * Real.log (x / (2 * π))) * Real.reciprocalSquarePair t x -
          xiZeroCountingMainTerm x * Real.reciprocalSquarePairSlope t x) x := by
    have hx' : t + H ≤ x := hx
    have hp : 0 < x := by linarith
    convert (hasDerivAt_xiZeroCountingMainTerm hp).mul
      (Real.hasDerivAt_reciprocalSquarePair (by linarith : x - t ≠ 0)
        (by linarith : x + t ≠ 0)) using 1
    unfold Real.reciprocalSquarePairSlope
    ring
  have hD := integrableOn_xiLehmanDensity ht hH
  have hP := integrableOn_xiCountingMain_mul_slope ht hH
  have hi : IntegrableOn (fun x =>
      ((1 / (2 * π)) * Real.log (x / (2 * π))) * Real.reciprocalSquarePair t x -
        xiZeroCountingMainTerm x * Real.reciprocalSquarePairSlope t x) (Ioi (t + H)) := by
    exact (hD.sub hP).congr_fun (fun _ _ => rfl) measurableSet_Ioi
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi (tendsto_xiCountingMain_mul_pair t)
  rw [integral_sub hD hP, integral_xiLehmanDensity_eq] at h
  linarith

end

end PrimeFactorUnimodality
