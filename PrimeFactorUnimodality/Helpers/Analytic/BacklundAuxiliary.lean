import PrimeNumberTheoremAnd.Backlund.ZeroCountCrude

/-! # The entire auxiliary function in Backlund's zero-count argument

Use `a(s)=(s-1)ζ(s)`, patched at one by its residue, and symmetrize the
translated powers as in Trudgian, arXiv:1208.5846, equation (2.4).
The real-axis values are exactly the real parts whose zeros control
horizontal argument variation. Analyticity and conjugation include the
patched pole; no zero-counting bound is assumed.

The entire surrogate and its differentiability proof are reused directly
from Robby Sneiderman's Apache-2.0 `Backlund.ZeroCountCrude` in the pinned
PNT revision `f6147e7572ab3abe5428101bc0b13627bcb005df`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex
open scoped ComplexConjugate

/-- The residue-patched entire surrogate respects conjugation, including at one. -/
theorem backlund_surrogate_conj (s : ℂ) :
    Backlund.zetaSurrogate (conj s) = conj (Backlund.zetaSurrogate s) := by
  by_cases hs : s = 1
  · simp [hs, Backlund.zetaSurrogate]
  have hc : conj s ≠ 1 := by
    intro h
    apply hs
    simpa using congrArg (starRingEnd ℂ) h
  simp only [Backlund.zetaSurrogate, ite_eq_right hs, ite_eq_right hc,
    riemannZeta_conj, map_mul, map_sub, map_one]

/-- The source's symmetrized powers of the entire zeta surrogate. -/
def backlundAuxiliary (T : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (Backlund.zetaSurrogate (z + T * I) ^ n + Backlund.zetaSurrogate (z - T * I) ^ n) / 2

/-- Every auxiliary function is entire, even when a translated argument equals the zeta pole. -/
theorem differentiable_backlundAuxiliary (T : ℝ) (n : ℕ) :
    Differentiable ℂ (backlundAuxiliary T n) := by
  apply Differentiable.div_const
  exact (((Backlund.zetaSurrogate_differentiable.comp
    (by fun_prop : Differentiable ℂ (fun z : ℂ => z + T * I))).pow n).add
      ((Backlund.zetaSurrogate_differentiable.comp
        (by fun_prop : Differentiable ℂ (fun z : ℂ => z - T * I))).pow n))

/-- On the real axis, the auxiliary function is the real part in the counting argument. -/
theorem backlundAuxiliary_ofReal (T σ : ℝ) (n : ℕ) :
    backlundAuxiliary T n σ = ((Backlund.zetaSurrogate ((σ : ℂ) + T * I) ^ n).re : ℂ) := by
  have hc : (σ : ℂ) - T * I = conj ((σ : ℂ) + T * I) := by simp [sub_eq_add_neg]
  unfold backlundAuxiliary
  rw [hc, backlund_surrogate_conj, ← map_pow]
  apply Complex.ext <;>
    simp only [div_ofNat_re, add_re, conj_re, ofReal_re,
      div_ofNat_im, add_im, conj_im, ofReal_im] <;> ring

/-- The auxiliary zeros on the real axis are exactly the real-part crossings. -/
theorem backlundAuxiliary_ofReal_eq_zero_iff (T σ : ℝ) (n : ℕ) :
    backlundAuxiliary T n σ = 0 ↔ (Backlund.zetaSurrogate ((σ : ℂ) + T * I) ^ n).re = 0 := by
  rw [backlundAuxiliary_ofReal, ofReal_eq_zero]

/-- Triangle inequality reduces its norm to the two translated surrogate powers. -/
theorem norm_backlundAuxiliary_le (T : ℝ) (n : ℕ) (z : ℂ) :
    ‖backlundAuxiliary T n z‖ ≤
      (‖Backlund.zetaSurrogate (z + T * I)‖ ^ n +
        ‖Backlund.zetaSurrogate (z - T * I)‖ ^ n) / 2 := by
  unfold backlundAuxiliary
  rw [norm_div, norm_ofNat]
  exact div_le_div_of_nonneg_right (by
    simpa only [norm_pow] using norm_add_le
      (Backlund.zetaSurrogate (z + T * I) ^ n) (Backlund.zetaSurrogate (z - T * I) ^ n))
    (by norm_num)

/-- A common bound on both translates controls every auxiliary power. -/
theorem norm_backlundAuxiliary_le_pow {T M : ℝ} {n : ℕ} {z : ℂ}
    (hp : ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    ‖backlundAuxiliary T n z‖ ≤ M ^ n := by
  apply (norm_backlundAuxiliary_le T n z).trans
  have hp' := pow_le_pow_left₀ (norm_nonneg _) hp n
  have hm' := pow_le_pow_left₀ (norm_nonneg _) hm n
  linarith

/-- The surrogate is nonzero at every centre to the right of the critical strip. -/
theorem backlund_surrogate_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    Backlund.zetaSurrogate s ≠ 0 := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  simp only [Backlund.zetaSurrogate, ite_eq_right hs1]
  exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_le_re hs.le)

end

end PrimeFactorUnimodality
