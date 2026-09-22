import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import PrimeNumberTheoremAnd.EulerMaclaurin

/-! # Exact Euler--Maclaurin remainder for the reciprocal partial sum

Factor the existing reciprocal-sum argument before choosing a norm bound.
Both the real-part and height-decaying digamma estimates use this identity,
including its two endpoints. The Euler--Maclaurin theorem is reused from
PNT revision `f6147e7572ab3abe5428101bc0b13627bcb005df`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

private theorem re_add_pos {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    0 < (z + x).re := by simp only [add_re, ofReal_re]; linarith

private theorem add_ne_zero {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    z + x ≠ 0 := by
  have h := re_add_pos hz hx
  intro he
  simp [he] at h

private theorem hasDerivAt_inv_add {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => (z + y)⁻¹) (-((z + x) ^ 2)⁻¹) x := by
  convert! ((hasDerivAt_inv (add_ne_zero hz hx)).comp (x : ℂ)
    ((hasDerivAt_id (x : ℂ)).const_add z)).comp_ofReal using 1
  simp

/-- The exact finite reciprocal-sum error, with no estimated endpoints or remainder. -/
theorem sum_inv_add_sub_log_eq_euler {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), (z + (k : ℂ))⁻¹) -
      (Complex.log (z + (N : ℂ)) - Complex.log z) =
        (z⁻¹ + (z + (N : ℂ))⁻¹) / 2 +
          ∫ x in (0 : ℝ)..N, -((z + x) ^ 2)⁻¹ * (B1 x : ℂ) := by
  let f (x : ℝ) : ℂ := (z + x)⁻¹
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hg : ContinuousOn (fun x : ℝ => -((z + x) ^ 2)⁻¹) (uIcc 0 (N : ℝ)) := by
    rw [uIcc_of_le hN]
    exact (((by fun_prop : ContinuousOn (fun x : ℝ => z + x) (Icc 0 (N : ℝ))).pow 2).inv₀
      (fun x hx => pow_ne_zero 2 (add_ne_zero hz hx.1))).neg
  have hcont : ContinuousOn (deriv f) (uIcc 0 (N : ℝ)) := by
    apply hg.congr
    intro x hx
    rw [uIcc_of_le hN] at hx
    exact (hasDerivAt_inv_add hz hx.1).deriv
  have he := sum_eq_integral_add_integral_deriv (f := f) (a := 0) (b := (N : ℝ))
    le_rfl hN (fun x hx => (hasDerivAt_inv_add hz hx.1).differentiableAt) hcont
  rw [show B1 0 = -(1 / 2 : ℝ) by norm_num [B1],
    show B1 (N : ℝ) = -(1 / 2 : ℝ) by norm_num [B1]] at he
  norm_num only [Nat.floor_zero, Nat.floor_natCast] at he
  have hset : insert 0 (Finset.Ioc 0 N) = Finset.range (N + 1) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_Ioc, Finset.mem_range]
    omega
  have hsplit : (∑ k ∈ Finset.range (N + 1), f k) = f 0 + ∑ k ∈ Finset.Ioc 0 N, f k := by
    rw [← hset, Finset.sum_insert (by simp), Nat.cast_zero]
  have hi : IntervalIntegrable f volume 0 (N : ℝ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hN
    exact (by fun_prop : ContinuousOn (fun x : ℝ => z + x) (Icc 0 (N : ℝ))).inv₀
      (fun x hx => add_ne_zero hz hx.1)
  have hlog : (∫ x in (0 : ℝ)..N, f x) = log (z + (N : ℂ)) - log z := by
    have hd (x : ℝ) (hx : x ∈ uIcc 0 (N : ℝ)) :
        HasDerivAt (fun y : ℝ => log (z + y)) (f x) x := by
      rw [uIcc_of_le hN] at hx
      convert! ((hasDerivAt_log (Or.inl (re_add_pos hz hx.1))).comp (x : ℂ)
        ((hasDerivAt_id (x : ℂ)).const_add z)).comp_ofReal using 1
      simp [f]
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have he' : (∑ k ∈ Finset.Ioc 0 N, f k) =
      -(f 0) / 2 + f N / 2 + (∫ x in (0 : ℝ)..N, f x) +
        ∫ x in (0 : ℝ)..N, deriv f x * (B1 x : ℂ) := by
    convert! he using 1
    push_cast
    ring_nf
    congr 1
  have hR : (∫ x in (0 : ℝ)..N, deriv f x * (B1 x : ℂ)) =
      ∫ x in (0 : ℝ)..N, -((z + x) ^ 2)⁻¹ * (B1 x : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hN] at hx
    dsimp only [f]
    rw [(hasDerivAt_inv_add hz hx.1).deriv]
  change (∑ k ∈ Finset.range (N + 1), f k) - _ = _
  rw [← hlog, hsplit, he', hR]
  simp only [f, ofReal_zero, add_zero, Complex.ofReal_natCast]
  ring

end

end PrimeFactorUnimodality
