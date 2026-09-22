/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.ZetaTrigonometric

/-! # Shifted trigonometric positivity for weighted von Mangoldt series

Nonnegative weights and a nonnegative cosine polynomial preserve positivity
after subtracting `κ` times a right-shifted series, provided `κ ≤ 1`.
The weighted theorem assumes convergence directly, so it also covers compactly
supported smoothing on lines inside the critical strip. The unweighted
logarithmic-derivative specialization requires real part greater than one.
-/

open Complex
open scoped BigOperators

private theorem shifted_exp_weight_nonneg (n : ℕ) {σ τ κ : ℝ}
    (hστ : σ ≤ τ) (hκ : κ ≤ 1) :
    0 ≤ Real.exp (-σ * Real.log n) - κ * Real.exp (-τ * Real.log n) := by
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have he : Real.exp (-τ * Real.log n) ≤ Real.exp (-σ * Real.log n) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_right hκ (Real.exp_pos (-τ * Real.log n)).le
  nlinarith

/-- Shifted positivity with arbitrary nonnegative smoothing weights on any convergent lines. -/
theorem sum_mul_re_shifted_weighted_vonMangoldt_nonneg {ι : Type*}
    (s : Finset ι) (a k : ι → ℝ) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    {σ τ κ : ℝ} (hστ : σ ≤ τ) (hκ : κ ≤ 1) (t : ℝ)
    (hσ : ∀ i, Summable (fun n => (w n : ℂ) *
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + (k i * t : ℝ) * I) n))
    (hτ : ∀ i, Summable (fun n => (w n : ℂ) *
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((τ : ℂ) + (k i * t : ℝ) * I) n))
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ s, a i * Real.cos (k i * u)) :
    0 ≤ ∑ i ∈ s, a i *
      ((∑' n, (w n : ℂ) * LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + (k i * t : ℝ) * I) n).re -
       κ * (∑' n, (w n : ℂ) * LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((τ : ℂ) + (k i * t : ℝ) * I) n).re) := by
  let T : ℝ → ι → ℕ → ℂ := fun r i n => (w n : ℂ) *
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      ((r : ℂ) + (k i * t : ℝ) * I) n
  have hσr (i : ι) : Summable (fun n => (T σ i n).re) :=
    (Complex.hasSum_re (hσ i).hasSum).summable
  have hτr (i : ι) : Summable (fun n => (T τ i n).re) :=
    (Complex.hasSum_re (hτ i).hasSum).summable
  have hσre (i : ι) : (∑' n, T σ i n).re = ∑' n, (T σ i n).re := re_tsum (hσ i)
  have hτre (i : ι) : (∑' n, T τ i n).re = ∑' n, (T τ i n).re := re_tsum (hτ i)
  change 0 ≤ ∑ i ∈ s, a i * ((∑' n, T σ i n).re - κ * (∑' n, T τ i n).re)
  simp_rw [hσre, hτre, ← tsum_mul_left,
    ← (hσr _).tsum_sub ((hτr _).mul_left κ)]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum
    (fun i _ => ((hσr i).sub ((hτr i).mul_left κ)).mul_left (a i))]
  apply tsum_nonneg
  intro n
  have hterm (r : ℝ) (i : ι) : (T r i n).re =
      w n * (ArithmeticFunction.vonMangoldt n * Real.exp (-r * Real.log n) *
        Real.cos (k i * t * Real.log n)) := by
    simp only [T, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      ArithmeticFunction.re_vonMangoldt_term]
  simp_rw [hterm]
  have heq : (∑ i ∈ s, a i *
      (w n * (ArithmeticFunction.vonMangoldt n * Real.exp (-σ * Real.log n) *
        Real.cos (k i * t * Real.log n)) -
       κ * (w n * (ArithmeticFunction.vonMangoldt n * Real.exp (-τ * Real.log n) *
        Real.cos (k i * t * Real.log n))))) =
      (w n * ArithmeticFunction.vonMangoldt n *
        (Real.exp (-σ * Real.log n) - κ * Real.exp (-τ * Real.log n))) *
          ∑ i ∈ s, a i * Real.cos (k i * (t * Real.log n)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc (k i) t (Real.log n)]
    ring
  rw [heq]
  exact mul_nonneg (mul_nonneg (mul_nonneg (hw n) ArithmeticFunction.vonMangoldt_nonneg)
    (shifted_exp_weight_nonneg n hστ hκ)) (hpoly _)

/-- Shifted logarithmic-derivative positivity in the half-plane of absolute convergence. -/
theorem sum_mul_re_shifted_neg_logDeriv_riemannZeta_nonneg {ι : Type*}
    (s : Finset ι) (a k : ι → ℝ) {σ τ κ : ℝ}
    (hσ : 1 < σ) (hστ : σ ≤ τ) (hκ : κ ≤ 1) (t : ℝ)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ s, a i * Real.cos (k i * u)) :
    0 ≤ ∑ i ∈ s, a i *
      ((-deriv riemannZeta ((σ : ℂ) + (k i * t : ℝ) * I) /
        riemannZeta ((σ : ℂ) + (k i * t : ℝ) * I)).re -
       κ * (-deriv riemannZeta ((τ : ℂ) + (k i * t : ℝ) * I) /
        riemannZeta ((τ : ℂ) + (k i * t : ℝ) * I)).re) := by
  have h := sum_mul_re_shifted_weighted_vonMangoldt_nonneg s a k (fun _ => 1)
    (fun _ => zero_le_one) hστ hκ t
    (fun i => by
      simpa only [ofReal_one, one_mul, LSeriesSummable] using
        (ArithmeticFunction.LSeriesSummable_vonMangoldt
          (show 1 < (((σ : ℂ) + (k i * t : ℝ) * I)).re by simpa using hσ)))
    (fun i => by
      simpa only [ofReal_one, one_mul, LSeriesSummable] using
        (ArithmeticFunction.LSeriesSummable_vonMangoldt
          (show 1 < (((τ : ℂ) + (k i * t : ℝ) * I)).re by simpa using hσ.trans_le hστ)))
    hpoly
  simp only [ofReal_one, one_mul] at h
  have heq (r : ℝ) (hr : 1 < r) (i : ι) :
      (∑' n, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((r : ℂ) + (k i * t : ℝ) * I) n) =
      -deriv riemannZeta ((r : ℂ) + (k i * t : ℝ) * I) /
        riemannZeta ((r : ℂ) + (k i * t : ℝ) * I) :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hr)
  simpa only [heq σ hσ, heq τ (hσ.trans_le hστ)] using h

/-- Finite smoothing weights make the von Mangoldt series converge at every complex point. -/
theorem summable_weighted_vonMangoldt_of_hasFiniteSupport {w : ℕ → ℝ}
    (hw : w.HasFiniteSupport) (s : ℂ) :
    Summable (fun n => (w n : ℂ) *
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n) := by
  apply summable_of_hasFiniteSupport
  apply hw.subset
  intro n hn
  contrapose! hn
  have hzero : w n = 0 := by simpa only [Function.mem_support, not_not] using hn
  simp [Function.mem_support, hzero]

/-- A real weight vanishing past a cutoff has finite support when sampled at `log n`. -/
theorem hasFiniteSupport_log_weight {f : ℝ → ℝ} {d : ℝ}
    (hf : ∀ x, d < x → f x = 0) : (fun n : ℕ => f (Real.log n)).HasFiniteSupport := by
  apply (Finset.range (⌈Real.exp d⌉₊ + 1)).finite_toSet.subset
  intro n hn
  by_contra hnmem
  have hnlarge : ⌈Real.exp d⌉₊ + 1 ≤ n := by
    simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hnmem
  have hlt : Real.exp d < (n : ℝ) := by
    have hceil := Nat.le_ceil (Real.exp d)
    have hncast : (⌈Real.exp d⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hnlarge
    linarith
  have hnpos : 0 < (n : ℝ) := (Real.exp_pos d).trans hlt
  exact hn (hf _ ((Real.lt_log_iff_exp_lt hnpos).mpr hlt))
