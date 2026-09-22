import PrimeFactorUnimodality.Helpers.Analytic.SmoothedXiRemainder
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Series.Imaginary

/-! # Summability of separated xi height tails

The unconditional shifted inverse-square norm theorem already proved for
the actual xi divisor controls height denominators outside a positive
cutoff. Multiplicities are retained. The tail uses `|γ| ≥ |t|+H`, exactly
Mossinghoff--Trudgian (4.1) for `t ≥ 0`, not the larger separated-height set.
This proves convergence, not a numerical zero-counting or Lehman bound.
Source: https://arxiv.org/pdf/1410.3926
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- Any divisor subset separated from the evaluation height has a summable height tail. -/
theorem summable_xi_height_inv_sq {P : RiemannXiDivisorZeroIndex → Prop} {H : ℝ}
    (hH : 0 < H) (t : ℝ)
    (hfar : ∀ p, P p → H ^ 2 ≤ (t - (riemannXiDivisorZeroValue p).im) ^ 2) :
    Summable (fun p : {p : RiemannXiDivisorZeroIndex // P p} =>
      1 / (t - (riemannXiDivisorZeroValue p.1).im) ^ 2) := by
  have hs := (summable_xi_divisor_shift_inv_sq ((t : ℂ) * I)).subtype P
  have hr (p : {p : RiemannXiDivisorZeroIndex // P p}) :
      |(((t : ℂ) * I) - riemannXiDivisorZeroValue p.1).re| ≤ 1 := by
    obtain ⟨hl, hu⟩ := riemannXi_zero_mem_critical_strip
      (riemannXiDivisorZeroValue_eq_zero p.1)
    simpa [abs_of_nonneg hl] using hu
  simpa using summable_inv_im_sq_of_norm_inv_sq hs hH hr
    (fun p => by simpa using hfar p.1 p.2)

/-- The paper's multiplicity-counted tail, with absolute height beyond `|t|+H`. -/
def xiHeightTail (t H : ℝ) : ℝ :=
  ∑' p : {p : RiemannXiDivisorZeroIndex //
    |t| + H ≤ |(riemannXiDivisorZeroValue p).im|},
    1 / (t - (riemannXiDivisorZeroValue p.1).im) ^ 2

/-- The height-tail definition is an actually convergent series for every positive cutoff. -/
theorem summable_xiHeightTail {H : ℝ} (hH : 0 < H) (t : ℝ) :
    Summable (fun p : {p : RiemannXiDivisorZeroIndex //
      |t| + H ≤ |(riemannXiDivisorZeroValue p).im|} =>
      1 / (t - (riemannXiDivisorZeroValue p.1).im) ^ 2) :=
  summable_xi_height_inv_sq hH t (fun _ hp => sq_le_sub_sq_of_abs_cutoff hH.le hp)

/-- All terms in a height tail are nonnegative. -/
theorem xiHeightTail_nonneg (t H : ℝ) : 0 ≤ xiHeightTail t H :=
  tsum_nonneg (fun _ => by positivity)

/-- Enlarging a divisor subset beyond the absolute cutoff increases the nonnegative tail. -/
theorem tsum_xi_height_inv_sq_le {P : RiemannXiDivisorZeroIndex → Prop} {H : ℝ}
    (hH : 0 < H) (t : ℝ)
    (hfar : ∀ p, P p → |t| + H ≤ |(riemannXiDivisorZeroValue p).im|) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // P p},
      1 / (t - (riemannXiDivisorZeroValue p.1).im) ^ 2) ≤ xiHeightTail t H := by
  let e : {p : RiemannXiDivisorZeroIndex // P p} →
      {p : RiemannXiDivisorZeroIndex //
        |t| + H ≤ |(riemannXiDivisorZeroValue p).im|} := fun p => ⟨p.1, hfar p.1 p.2⟩
  have he : Function.Injective e := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun r => r.val) h
  exact Summable.tsum_le_tsum_of_inj e he (fun _ _ => by positivity) (fun _ => le_rfl)
    (summable_xi_height_inv_sq hH t
      (fun p hp => sq_le_sub_sq_of_abs_cutoff hH.le (hfar p hp))) (summable_xiHeightTail hH t)

end

end PrimeFactorUnimodality
