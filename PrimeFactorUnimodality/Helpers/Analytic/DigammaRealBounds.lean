import Mathlib.Analysis.SumIntegralComparisons
import PrimeFactorUnimodality.Helpers.Analytic.DigammaLogBounds

/-! # One-sided logarithmic bounds on real digamma

Mathlib's decreasing sum--integral comparison bounds the reciprocal partial
sums from below. Their already-proved limit, obtained from the pinned PNT
digamma series, gives the sharper upper bound on the positive real axis.
No error term is needed on that side of the inequality.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter Set
open scoped Topology

/-- On the positive real axis, digamma is bounded above by the logarithm itself. -/
theorem re_digamma_ofReal_le_log {x : ℝ} (hx : 0 < x) :
    (digamma (x : ℂ)).re ≤ Real.log x := by
  have hsum (N : ℕ) : Real.log (x + (N + 1 : ℕ)) - Real.log x ≤
      ∑ k ∈ Finset.range (N + 1), (x + (k : ℝ))⁻¹ := by
    have hm : AntitoneOn (fun u : ℝ => u⁻¹) (Icc x (x + (N + 1 : ℕ))) :=
      fun u hu v _ huv => inv_anti₀ (hx.trans_le hu.1) huv
    have h := hm.integral_le_sum
    rw [integral_inv_of_pos hx (by positivity), Real.log_div (by positivity) hx.ne'] at h
    exact h
  have hlim := continuous_re.continuousAt.tendsto.comp
    ((tendsto_sum_inv_add_sub_log (z := (x : ℂ)) hx).sub
      (Complex.tendsto_log_add_nat_sub_log_nat_add_one ((x : ℂ) + 1)))
  have hreal : Tendsto (fun N : ℕ =>
      (∑ k ∈ Finset.range (N + 1), (x + (k : ℝ))⁻¹) -
        Real.log (x + (N + 1 : ℕ))) atTop (𝓝 (-(digamma (x : ℂ)).re)) := by
    convert! hlim using 1
    · funext N
      have he : (x : ℂ) + 1 + N = ((x + (N + 1 : ℕ) : ℝ) : ℂ) := by
        push_cast
        ring
      simp only [Function.comp_apply, sub_re, ofReal_re, he, Complex.log_re, norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity : 0 < x + (N + 1 : ℕ))]
      rw [show (∑ k ∈ Finset.range (N + 1), ((x : ℂ) + k)⁻¹).re =
        ∑ k ∈ Finset.range (N + 1), (((x : ℂ) + k)⁻¹).re from
          map_sum Complex.reAddGroupHom _ _]
      have hs : (∑ k ∈ Finset.range (N + 1), (((x : ℂ) + k)⁻¹).re) =
          ∑ k ∈ Finset.range (N + 1), (x + (k : ℝ))⁻¹ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← ofReal_natCast, ← ofReal_add, ← ofReal_inv, ofReal_re]
      rw [hs]
      ring
    · simp
  have hb : -Real.log x ≤ -(digamma (x : ℂ)).re :=
    ge_of_tendsto hreal (Filter.Eventually.of_forall (fun N => by linarith [hsum N]))
  linarith

end

end PrimeFactorUnimodality
