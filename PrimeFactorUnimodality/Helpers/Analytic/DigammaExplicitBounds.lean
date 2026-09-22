import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

set_option autoImplicit false

/-! # Explicit real-part bounds for the gamma logarithmic derivative

Split the convergent digamma series at an arbitrary positive integer. The
real part of the head is bounded by a harmonic number; the tail is bounded
by `‖z - 1‖ / N`. The Euler constant cancels against the harmonic estimate.
Choosing the splitting point explicitly gives a logarithmic bound with
unit coefficient, and hence coefficient `1/2` for the zeta gamma factor.

The series and inverse-square tail primitives are Robby Sneiderman's
Apache-2.0 development in `kimihiro64/PrimeNumberTheoremAnd`, revision
`f6147e7572ab3abe5428101bc0b13627bcb005df`, module `DigammaSeries`.
We use `Complex.hasSum_digamma_of_re_pos`,
`Complex.inv_add_one_sub_inv_eq`, and
`Complex.tsum_one_div_natCast_add_add_one_sq_le` without renaming them.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Finset
open scoped BigOperators

private theorem norm_digamma_term_le {z : ℂ} (hz : 1 ≤ z.re) (n : ℕ) :
    ‖((n : ℂ) + 1)⁻¹ - (z + n)⁻¹‖ ≤ ‖z - 1‖ / ((n : ℝ) + 1) ^ 2 := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hzn : 0 < (z + n).re := by simp only [add_re, natCast_re]; positivity
  have hne : z + n ≠ 0 := by intro h; simp [h] at hzn
  have hnorm : (n : ℝ) + 1 ≤ ‖z + n‖ := by
    have := re_le_norm (z + n)
    simp only [add_re, natCast_re] at this
    linarith
  rw [inv_add_one_sub_inv_eq hne, norm_mul, norm_inv, norm_mul,
    norm_natCast_add_one, ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hn)
  nlinarith

/-- The norm of the digamma-series tail has a fully explicit bound. -/
theorem norm_digamma_series_tail_le {z : ℂ} (hz : 1 ≤ z.re)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖∑' i : ℕ, ((((i + N : ℕ) : ℂ) + 1)⁻¹ - (z + (i + N : ℕ))⁻¹)‖ ≤
      ‖z - 1‖ / N := by
  have hmaj : Summable (fun n : ℕ => ‖z - 1‖ / ((n : ℝ) + 1) ^ 2) := by
    simpa only [mul_one_div] using
      Complex.summable_one_div_natCast_add_one_sq.mul_left ‖z - 1‖
  have hnorm : Summable (fun n : ℕ => ‖((n : ℂ) + 1)⁻¹ - (z + n)⁻¹‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_digamma_term_le hz) hmaj
  have hs := (summable_nat_add_iff N).mpr hnorm
  have hm := (summable_nat_add_iff N).mpr hmaj
  calc
    _ ≤ ∑' i : ℕ, ‖(((i + N : ℕ) : ℂ) + 1)⁻¹ - (z + (i + N : ℕ))⁻¹‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' i : ℕ, ‖z - 1‖ / (((i + N : ℕ) : ℝ) + 1) ^ 2 :=
      hs.tsum_le_tsum (fun i => norm_digamma_term_le hz (i + N)) hm
    _ = ‖z - 1‖ * ∑' i : ℕ, 1 / (((i + N : ℕ) : ℝ) + 1) ^ 2 := by
      rw [← tsum_mul_left]
      exact tsum_congr fun _ => (mul_one_div _ _).symm
    _ ≤ ‖z - 1‖ * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (Complex.tsum_one_div_natCast_add_add_one_sq_le hN) (norm_nonneg _)
    _ = ‖z - 1‖ / N := (div_eq_mul_inv _ _).symm

/-- A free splitting point allows later gamma-factor estimates to optimize the constant. -/
theorem re_digamma_le_log_add_tail {z : ℂ} (hz : 1 ≤ z.re)
    {N : ℕ} (hN : 1 ≤ N) :
    (digamma z).re ≤ Real.log ((N : ℝ) + 1) + ‖z - 1‖ / N := by
  have hsum := Complex.hasSum_digamma_of_re_pos (lt_of_lt_of_le zero_lt_one hz)
  have hsplit := hsum.summable.sum_add_tsum_nat_add N
  have hhead : (∑ n ∈ range N, (((n : ℂ) + 1)⁻¹ - (z + n)⁻¹)).re ≤
      (harmonic N : ℝ) := by
    rw [show (∑ n ∈ range N, (((n : ℂ) + 1)⁻¹ - (z + n)⁻¹)).re =
      ∑ n ∈ range N, (((n : ℂ) + 1)⁻¹ - (z + n)⁻¹).re from map_sum Complex.reAddGroupHom _ _]
    rw [← Complex.sum_inv_natCast_add_one_real]
    apply sum_le_sum
    intro n hn
    have hpos : 0 ≤ (z + n).re := by
      simp only [add_re, natCast_re]
      positivity
    have hinv : 0 ≤ ((z + n)⁻¹).re := by
      rw [inv_re]
      exact div_nonneg hpos (normSq_nonneg _)
    have hre : (((n : ℂ) + 1)⁻¹).re = ((n : ℝ) + 1)⁻¹ := by
      rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
        ← ofReal_inv, ofReal_re]
    rw [sub_re, hre]
    exact sub_le_self _ hinv
  have htail := (re_le_norm _).trans (norm_digamma_series_tail_le hz hN)
  have hreal := congrArg Complex.re hsplit
  rw [hsum.tsum_eq] at hreal
  simp only [add_re, ofReal_re] at hreal
  have hH := (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N).le
  change (harmonic N : ℝ) - Real.log ((N : ℝ) + 1) ≤
    Real.eulerMascheroniConstant at hH
  linarith

/-- Unit-coefficient logarithmic growth, with no unspecified constants or threshold. -/
theorem re_digamma_le_log_norm_sub_one_add_two {z : ℂ} (hz : 1 ≤ z.re) :
    (digamma z).re ≤ Real.log (‖z - 1‖ + 2) + 1 := by
  let N : ℕ := max 1 ⌈‖z - 1‖⌉₊
  have hN : 1 ≤ N := le_max_left _ _
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hR : ‖z - 1‖ ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈‖z - 1‖⌉₊))
  have hupper : (N : ℝ) ≤ ‖z - 1‖ + 1 := by
    dsimp [N]
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith [norm_nonneg (z - 1)])
      (Nat.ceil_lt_add_one (norm_nonneg (z - 1))).le
  apply (re_digamma_le_log_add_tail hz hN).trans
  apply add_le_add
  · exact Real.log_le_log (by positivity) (by linarith)
  · exact (div_le_one hNpos).mpr hR

/-- Explicit gamma-factor bound on the full half-plane needed by the zero-free argument. -/
theorem re_zeta_gamma_factor_le {s : ℂ} (hs : 0 ≤ s.re) :
    (-(1 / 2 : ℂ) * Real.log Real.pi +
      (1 / 2 : ℂ) * digamma (s / 2 + 1)).re ≤
        (1 / 2 : ℝ) * Real.log (‖s‖ / 2 + 2) + 1 / 2 -
          (1 / 2 : ℝ) * Real.log Real.pi := by
  have hz : 1 ≤ (s / 2 + 1).re := by simp only [add_re, div_ofNat_re, one_re]; linarith
  have h := re_digamma_le_log_norm_sub_one_add_two hz
  simp only [add_sub_cancel_right, norm_div, norm_ofNat] at h
  simp only [add_re, mul_re, neg_re, div_ofNat_re, one_re, ofReal_re, ofReal_im,
    mul_zero, sub_zero, neg_im, div_ofNat_im, one_im, zero_div, neg_zero, zero_mul]
  linarith

/-- Vertical-strip version; the logarithm has the required coefficient `1/2`. -/
theorem re_zeta_gamma_factor_le_vertical {s : ℂ} (hs : 0 ≤ s.re) (hs₂ : s.re ≤ 2) :
    (-(1 / 2 : ℂ) * Real.log Real.pi +
      (1 / 2 : ℂ) * digamma (s / 2 + 1)).re ≤
        (1 / 2 : ℝ) * Real.log (|s.im| / 2 + 3) + 1 / 2 -
          (1 / 2 : ℝ) * Real.log Real.pi := by
  apply (re_zeta_gamma_factor_le hs).trans
  have hn := norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg hs] at hn
  have hl : Real.log (‖s‖ / 2 + 2) ≤ Real.log (|s.im| / 2 + 3) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

end

end PrimeFactorUnimodality
