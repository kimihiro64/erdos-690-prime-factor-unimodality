import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeFactorUnimodality.Helpers.Analytic.ThetaFromPsi

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

open Filter Set
open scoped Topology

/-! A quantitative interface for the error term supplied by an explicit
prime-number theorem.  The point of this definition is that it records the
analytic estimate itself, rather than treating the desired log-fourth bound
as an imported theorem. -/
def HasPsiSqrtLogDecay (C c X : Real) : Prop :=
  ∀ x : Real, X ≤ x →
    |Chebyshev.psi x - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))

private theorem sqrtLog_pow_eight_eq_log_pow_four
    {t : Real} (ht : 0 ≤ t) :
    (Real.sqrt t) ^ (8 : ℕ) = t ^ (4 : ℕ) := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul]
  rw [show (Real.sqrt t) ^ 2 = t by exact Real.sq_sqrt ht]

/-! Exponential square-root-log decay is eventually stronger than every fixed
power of `log`.  This is the analytic conversion needed before an explicit
finite cutoff is supplied. -/
theorem exists_hasPsiLogFourthError_of_sqrtLogDecay
    {C c X : Real} (hC : 0 ≤ C) (hc : 0 < c) (hX : 0 < X)
    (hdecay : HasPsiSqrtLogDecay C c X) :
    ∃ Y : Real, X ≤ Y ∧ HasPsiLogFourthError 1 Y := by
  by_cases hCzero : C = 0
  · refine ⟨X, le_rfl, ?_⟩
    intro x hx
    have hzero : |Chebyshev.psi x - x| ≤ 0 := by
      simpa [hCzero] using hdecay x hx
    have hx_nonneg : 0 ≤ x := (lt_of_lt_of_le hX hx).le
    have habs : |Chebyshev.psi x - x| = 0 := le_antisymm hzero (abs_nonneg _)
    rw [habs]
    exact div_nonneg (by positivity) (by positivity)
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have hdecay_zero :
        Tendsto (fun t : Real => t ^ (8 : Real) * Real.exp (-c * t))
          atTop (𝓝 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 8 c hc
    have hsqrt_atTop : Tendsto (fun t : Real => Real.sqrt t) atTop atTop := by
      simpa [Real.sqrt_eq_rpow] using
        (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 2))
    have hdecay_sqrt :
        Tendsto (fun t : Real => (Real.sqrt t) ^ (8 : Real) *
          Real.exp (-c * Real.sqrt t)) atTop (𝓝 0) := by
      exact hdecay_zero.comp hsqrt_atTop
    have hsmall : ∀ᶠ t : Real in atTop,
        (Real.sqrt t) ^ (8 : Real) * Real.exp (-c * Real.sqrt t) < C⁻¹ := by
      apply (hdecay_sqrt.eventually (show Set.Iio C⁻¹ ∈ 𝓝 (0 : Real) by
        exact Iio_mem_nhds (inv_pos.mpr hCpos))).mono
      intro t ht
      exact ht
    obtain ⟨T, hT⟩ := (eventually_atTop.1 hsmall)
    let Y : Real := max X (max (Real.exp T) 2)
    refine ⟨Y, le_max_left _ _, ?_⟩
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le hX (le_trans (le_max_left _ _) hx)
    have hY_le_x : Y ≤ x := hx
    have hmax_le_x : max (Real.exp T) 2 ≤ x :=
      le_trans (le_max_right X (max (Real.exp T) 2)) hY_le_x
    have hT_exp : Real.exp T ≤ x :=
      le_trans (le_max_left (Real.exp T) 2) hmax_le_x
    have hx_two : (2 : Real) ≤ x :=
      le_trans (le_max_right (Real.exp T) 2) hmax_le_x
    have hT_log : T ≤ Real.log x := by
      exact (Real.le_log_iff_exp_le hx_pos).2 hT_exp
    have hlog_nonneg : 0 ≤ Real.log x := by
      exact (Real.log_pos (by linarith)).le
    have hsmall_x := hT (Real.log x) hT_log
    have hpow := sqrtLog_pow_eight_eq_log_pow_four hlog_nonneg
    have hbound :
        C * Real.exp (-c * Real.sqrt (Real.log x)) ≤
          1 / (Real.log x) ^ (4 : ℕ) := by
      have hmul := (mul_lt_mul_of_pos_left hsmall_x hCpos).le
      have hpow' : (Real.sqrt (Real.log x)) ^ (8 : Real) =
          (Real.log x) ^ (4 : ℕ) := by
        simpa [Real.rpow_natCast] using hpow
      have hmul' : C * ((Real.log x) ^ (4 : ℕ) *
          Real.exp (-c * Real.sqrt (Real.log x))) ≤ C * C⁻¹ := by
        calc
          C * ((Real.log x) ^ (4 : ℕ) *
              Real.exp (-c * Real.sqrt (Real.log x))) =
              C * ((Real.sqrt (Real.log x)) ^ (8 : Real) *
                Real.exp (-c * Real.sqrt (Real.log x))) := by rw [hpow']
          _ ≤ C * C⁻¹ := hmul
      have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
      have hlog4_pos : 0 < (Real.log x) ^ (4 : ℕ) := by positivity
      have hmul'' : C * Real.exp (-c * Real.sqrt (Real.log x)) *
          (Real.log x) ^ (4 : ℕ) ≤ 1 := by
        calc
          C * Real.exp (-c * Real.sqrt (Real.log x)) *
              (Real.log x) ^ (4 : ℕ) =
              C * ((Real.log x) ^ (4 : ℕ) *
                Real.exp (-c * Real.sqrt (Real.log x))) := by ring
          _ ≤ 1 := by simpa [hCpos.ne'] using hmul'
      exact (le_div_iff₀ hlog4_pos).2 hmul''
    calc
      |Chebyshev.psi x - x| ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := hdecay x
            (le_trans (le_max_left _ _) hx)
      _ = (C * Real.exp (-c * Real.sqrt (Real.log x))) * x := by ring
      _ ≤ (1 / (Real.log x) ^ (4 : ℕ)) * x :=
        mul_le_mul_of_nonneg_right hbound hx_pos.le
      _ = 1 * x / (Real.log x) ^ 4 := by ring

end

end PrimeFactorUnimodality
