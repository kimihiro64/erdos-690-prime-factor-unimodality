import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanRemainder
import PrimeFactorUnimodality.Helpers.Analytic.XiZetaCountingBridge

/-! # Transfer of explicit zeta counting estimates to the Lehman tail

Transfer a Riemann-von Mangoldt estimate through the proved strict/closed
bridge. The `7/8` offset is kept explicitly. The usual Backlund constants
imply the required `2 log T` envelope once `log T >= 5`. The underlying
Riemann-von Mangoldt estimate remains an explicit hypothesis, not a proved
numerical input of this module.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Filter Real Set
open scoped Topology

/-- A continuous RvM envelope transfers to the closed count even at a zero ordinate. -/
theorem xiZeroCount_rvm_le {b₁ b₂ b₃ T : ℝ}
    (h : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃) (hT : 2 ≤ T) :
    |(xiZeroCount T : ℝ) - (xiZeroCountingMainTerm T + 7 / 8)| ≤
      riemannZeta.RvM b₁ b₂ b₃ T := by
  have hTpos : 0 < T := by linarith
  have hl := Real.continuousAt_log hTpos.ne'
  have hll : ContinuousAt (fun x => Real.log (Real.log x)) T :=
    (Real.continuousAt_log (Real.log_pos (by linarith : 1 < T)).ne').comp hl
  apply xiZeroCount_error_le_of_strict
    ((hasDerivAt_xiZeroCountingMainTerm hTpos).continuousAt.add continuousAt_const)
    ((continuousAt_const.mul hl).add (continuousAt_const.mul hll) |>.add continuousAt_const)
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [xiStrictZeroCount_eq_zeta_N]
  exact h x (hT.trans (show T < x from hx).le)

/-- Removing the conventional main-term offset costs exactly `7/8` in the error bound. -/
theorem xiZeroCountingRemainder_le_rvm_add {b₁ b₂ b₃ T : ℝ}
    (h : riemannZeta.Riemann_vonMangoldt_bound b₁ b₂ b₃) (hT : 2 ≤ T) :
    |xiZeroCountingRemainder T| ≤ riemannZeta.RvM b₁ b₂ b₃ T + 7 / 8 := by
  have heq : xiZeroCountingRemainder T =
      ((xiZeroCount T : ℝ) - (xiZeroCountingMainTerm T + 7 / 8)) + 7 / 8 := by
    unfold xiZeroCountingRemainder
    ring
  rw [heq]
  calc
    _ ≤ |(xiZeroCount T : ℝ) - (xiZeroCountingMainTerm T + 7 / 8)| + |(7 / 8 : ℝ)| :=
      abs_add_le _ _
    _ ≤ _ := by norm_num; exact xiZeroCount_rvm_le h hT

/-- A purely algebraic envelope comparison; no count estimate or certificate is used. -/
theorem backlund_envelope_add_offset_le_two_log {T : ℝ} (hlog : 5 ≤ Real.log T) :
    riemannZeta.RvM 0.137 0.443 6.1 T + 7 / 8 ≤ 2 * Real.log T := by
  have hll := Real.log_le_self (by linarith : 0 ≤ Real.log T)
  unfold riemannZeta.RvM
  linarith

/-- The stated Backlund estimate supplies the actual closed counting-error bound. -/
theorem xiZeroCountingRemainder_le_two_log_of_rvm
    (h : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    {A : ℝ} (hA : 2 ≤ A) (hlog : 5 ≤ Real.log A) :
    ∀ x ∈ Ici A, |xiZeroCountingRemainder x| ≤ 2 * Real.log x := by
  intro x hx
  exact (xiZeroCountingRemainder_le_rvm_add h (hA.trans hx)).trans
    (backlund_envelope_add_offset_le_two_log
      (hlog.trans (Real.log_le_log (by linarith : 0 < A) hx)))

/-- The actual closed Lehman tail inherits the estimate and its exact boundary atom. -/
theorem xiHeightTail_le_of_rvm
    (h : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1)
    {t H : ℝ} (ht : 0 < t) (hH : 0 < H) (hA : 2 ≤ t + H)
    (hlog : 5 ≤ Real.log (t + H)) :
    xiHeightTail t H ≤ xiLehmanMainIntegral t H + xiLehmanIntegralCorrection t H +
      (xiOrdinateMultiplicity (t + H) : ℝ) * Real.reciprocalSquarePair t (t + H) :=
  xiHeightTail_le_main_add_correction_of_counting_error ht hH
    (xiZeroCountingRemainder_le_two_log_of_rvm h hA hlog)

end

end PrimeFactorUnimodality
