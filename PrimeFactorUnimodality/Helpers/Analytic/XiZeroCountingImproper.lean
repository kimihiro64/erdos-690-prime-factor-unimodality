import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingLimits

/-! # Improper Abel integrals for actual xi zeros

Pass the finite actual counting identity to infinity. For a nonpositive
derivative, the existing summable zero series and vanishing counting
boundary prove absolute integrability of the counting integral itself.
No numerical counting bound is needed for this step.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- Integrability and the exact infinite Abel formula follow from the finite identity. -/
theorem xi_strict_tail_eq_integral_of_count_boundary {a : ℝ} (ha : 0 ≤ a) {f g : ℝ → ℝ}
    (hs : Summable (fun p : {p : RiemannXiDivisorZeroIndex //
      a < (riemannXiDivisorZeroValue p).im} => f (riemannXiDivisorZeroValue p.1).im))
    (hf : ∀ x ∈ Ici a, HasDerivAt f (g x) x)
    (hg : ∀ b, IntegrableOn g (Icc a b)) (hgneg : ∀ x ∈ Ioi a, g x ≤ 0)
    (hboundary : Tendsto (fun T => (xiZeroCount T : ℝ) * f T) atTop (𝓝 0)) :
    IntegrableOn (fun x => (xiZeroCount x : ℝ) * g x) (Ioi a) ∧
      (∑' p : {p : RiemannXiDivisorZeroIndex // a < (riemannXiDivisorZeroValue p).im},
        f (riemannXiDivisorZeroValue p.1).im) =
        -(xiZeroCount a : ℝ) * f a - ∫ x in Ioi a, (xiZeroCount x : ℝ) * g x := by
  let S := ∑' p : {p : RiemannXiDivisorZeroIndex // a < (riemannXiDivisorZeroValue p).im},
    f (riemannXiDivisorZeroValue p.1).im
  have hlocal (b : ℝ) := integrableOn_xiZeroCount_mul (hg b)
  have hfinite (b : ℝ) (hab : a ≤ b) := sum_xi_height_window_eq_boundary_sub_integral hab
    (fun x hx => hf x hx.1) (hg b)
  have hnorm (b : ℝ) (hab : a ≤ b) :
      (∫ x in a..b, ‖(xiZeroCount x : ℝ) * g x‖) =
        (∑ p ∈ xiHeightWindowIndices a b, f (riemannXiDivisorZeroValue p).im) -
          (xiZeroCount b : ℝ) * f b + (xiZeroCount a : ℝ) * f a := by
    have he : (∫ x in a..b, ‖(xiZeroCount x : ℝ) * g x‖) =
        -(∫ x in Icc a b, (xiZeroCount x : ℝ) * g x) := by
      rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc, ← integral_neg]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only
      exact Real.norm_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hgneg x hx.1))
    rw [he]
    linarith [hfinite b hab]
  have hlimit : Tendsto (fun b => ∫ x in a..b, ‖(xiZeroCount x : ℝ) * g x‖) atTop
      (𝓝 (S + (xiZeroCount a : ℝ) * f a)) := by
    have h := ((tendsto_sum_xi_height_window ha hs).sub hboundary).add_const
      ((xiZeroCount a : ℝ) * f a)
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop a] with b hb
    exact (hnorm b hb).symm
  have hint : IntegrableOn (fun x => (xiZeroCount x : ℝ) * g x) (Ioi a) :=
    integrableOn_Ioi_of_intervalIntegral_norm_tendsto _ a
      (fun b => (hlocal b).mono_set Ioc_subset_Icc_self) tendsto_id hlimit
  refine ⟨hint, ?_⟩
  have hnormlimit := intervalIntegral_tendsto_integral_Ioi a hint.norm tendsto_id
  have hv := tendsto_nhds_unique hlimit hnormlimit
  have he : (∫ x in Ioi a, ‖(xiZeroCount x : ℝ) * g x‖) =
      -(∫ x in Ioi a, (xiZeroCount x : ℝ) * g x) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    exact Real.norm_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hgneg x hx))
  rw [he] at hv
  change S = _
  linarith

end

end PrimeFactorUnimodality
