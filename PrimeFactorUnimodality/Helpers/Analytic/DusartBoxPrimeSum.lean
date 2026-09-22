import Mathlib.NumberTheory.Chebyshev
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxCutoff
import PrimeFactorUnimodality.Helpers.Analytic.StechkinBasic
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageAlgebra

/-! # The box cutoff's arithmetic side is the actual Chebyshev average

On a fixed averaging support, the Chebyshev sum is a single finite sum of
translated steps. Averaging that finite sum identifies the logarithmic
cutoff weights exactly. The zero-parameter Dirichlet series is then the
same average, with no numerical or explicit-formula premise.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real intervalIntegral
open scoped BigOperators

/-- A common finite index set represents every Chebyshev sum below its upper endpoint. -/
theorem psi_eq_sum_dusartUnitStep {y : ℝ} {N : ℕ} (hy : 0 ≤ y) (hN : y ≤ N) :
    ψ y = ∑ n ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt n *
      dusartUnitStep (y - n) := by
  classical
  have hs : (Finset.Icc 0 N).filter (fun n : ℕ => (n : ℝ) ≤ y) = Finset.Icc 0 ⌊y⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.zero_le, true_and, Nat.le_floor_iff hy]
    exact ⟨fun hn => hn.2, fun hn => ⟨by exact_mod_cast hn.trans hN, hn⟩⟩
  rw [psi_eq_sum_Icc, ← hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : (n : ℝ) ≤ y <;> simp [dusartUnitStep, sub_nonneg, hn]

/-- Exact finite-sum evaluation of the actual iterated Chebyshev average. -/
theorem dusart_psi_average_eq_sum (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 0 ≤ x)
    {N : ℕ} (hN : x + (m + 3 : ℕ) * h ≤ N) :
    iteratedBoxAverage h (m + 3) ψ x =
      ∑ n ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt n *
        dusartBoxDistribution m h (x - n) := by
  let f : ℕ → ℝ → ℝ := fun n y => ArithmeticFunction.vonMangoldt n * dusartUnitStep (y - n)
  have hmono (n : ℕ) : Monotone (f n) := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left (monotone_dusartUnitStep (by linarith))
      ArithmeticFunction.vonMangoldt_nonneg
  have he : Set.EqOn ψ (fun y => ∑ n ∈ Finset.Icc 0 N, f n y)
      (Set.Icc x (x + (m + 3 : ℕ) * h)) := by
    intro y hy
    exact psi_eq_sum_dusartUnitStep (hx.trans hy.1) (hy.2.trans hN)
  rw [iteratedBoxAverage_congr_on hh.le (m + 3) he,
    iteratedBoxAverage_sum hh (m + 3) _ f (fun n _ => hmono n)]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only [f]
  rw [iteratedBoxAverage_const_mul]
  congr 1
  simpa only [sub_eq_add_neg, dusartBoxDistribution] using
    iteratedBoxAverage_translate h (m + 3) dusartUnitStep (-(n : ℝ)) x

/-- The compactly smoothed Mangoldt series at zero is precisely the Chebyshev box average. -/
theorem smoothedVonMangoldt_box_zero_eq_average (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 0 < x) :
    smoothedVonMangoldt (dusartBoxWeight m h x) 0 =
      (iteratedBoxAverage h (m + 3) ψ x : ℂ) := by
  classical
  let N : ℕ := ⌈x + (m + 3 : ℕ) * h⌉₊
  have hN : x + (m + 3 : ℕ) * h ≤ N := Nat.le_ceil _
  have hU : 0 < x + (m + 3 : ℕ) * h :=
    add_pos_of_pos_of_nonneg hx (mul_nonneg (Nat.cast_nonneg _) hh.le)
  rw [dusart_psi_average_eq_sum m hh hx.le hN, Complex.ofReal_sum]
  unfold smoothedVonMangoldt
  calc
    _ = ∑ n ∈ Finset.Icc 0 N, (dusartBoxWeight m h x (log n) : ℂ) *
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 0 n := by
      apply tsum_eq_sum
      intro n hn
      have hNn : N < n := by simpa only [Finset.mem_Icc, Nat.zero_le, true_and, not_le] using hn
      have hUn : x + (m + 3 : ℕ) * h < n := hN.trans_lt (by exact_mod_cast hNn)
      have hnpos : 0 < (n : ℝ) := hU.trans hUn
      have hw : dusartBoxWeight m h x (log n) = 0 := by
        unfold dusartBoxWeight
        rw [exp_log hnpos]
        apply dusartBoxDistribution_eq_zero m hh
        linarith
      simp [hw]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : n = 0
      · subst n
        simp
      · rw [LSeries.term_of_ne_zero hn, Complex.cpow_zero, div_one]
        have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        simp only [dusartBoxWeight, exp_log hnpos, Complex.ofReal_mul]
        ring

end

end PrimeFactorUnimodality
