import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaTimeAliasing

set_option autoImplicit false

/-! # Geometric bounds for omitted sinc samples

Tangents to the two polynomial Gaussians are taken at the first omitted
sample radius. Their positive decay rates give closed sums, without a
large intermediate normalization or unevaluated incomplete Gamma integral.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The logarithmic decay rate of each Gaussian polynomial at the cutoff. -/
def plattSincTailRate (k : ℕ) (h R : ℝ) (i : Bool) : ℝ :=
  R / h ^ 2 - (plattZetaTimeDegree k i : ℝ) / R

/-- The value of each positive Gaussian majorant at the first omitted sample. -/
def plattSincTailCoeff (k : ℕ) (t₀ h R : ℝ) (i : Bool) : ℝ :=
  plattZetaTimeCoeff k t₀ i * R ^ plattZetaTimeDegree k i *
    Real.exp (-(1 / (2 * h ^ 2)) * R ^ 2)

/-- A common summable majorant for both tails after the cutoff. -/
def plattSincTailMajorant (k : ℕ) (t₀ h A R : ℝ) (n : ℕ) : ℝ :=
  ∑ i : Bool, plattSincTailCoeff k t₀ h R i *
    Real.exp (-plattSincTailRate k h R i * ((n : ℝ) / A))

/-- The combined majorant sum for both omitted tails. -/
def plattSincTailError (k : ℕ) (t₀ h A R : ℝ) : ℝ :=
  2 * ∑ i : Bool, plattSincTailCoeff k t₀ h R i /
    (1 - Real.exp (-plattSincTailRate k h R i / A))

/-- The larger polynomial degree controls the positivity of both tangent rates. -/
theorem plattSincTailRate_pos (k : ℕ) {h R : ℝ} (hh : 0 < h) (hR : 0 < R)
    (hk : ((k : ℝ) + 1) * h ^ 2 < R ^ 2) (i : Bool) :
    0 < plattSincTailRate k h R i := by
  have hd : (plattZetaTimeDegree k i : ℝ) ≤ (k : ℝ) + 1 := by
    cases i <;> simp [plattZetaTimeDegree]
  unfold plattSincTailRate
  apply sub_pos.mpr
  apply (div_lt_div_iff₀ hR (by positivity : 0 < h ^ 2)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg h)]

/-- The genuine window is bounded at either sign of each omitted sample. -/
theorem norm_plattZetaWindow_le_sincTailMajorant (k : ℕ) (t₀ : ℝ) {h A R v : ℝ}
    (hh : 0 < h) (hA : 0 < A) (hR : 0 < R) (n : ℕ)
    (hv : |v| = (n : ℝ) / A + R) :
    ‖plattZetaWindow k t₀ h v‖ ≤ plattSincTailMajorant k t₀ h A R n := by
  apply (norm_plattZetaWindow_le_polynomialGaussian k t₀ h v).trans
  unfold plattSincTailMajorant
  apply Finset.sum_le_sum
  intro i hi
  have he : (plattZetaTimeDegree k i : ℝ) / R - 2 * (1 / (2 * h ^ 2)) * R =
      -plattSincTailRate k h R i := by unfold plattSincTailRate; ring
  have ht := mul_le_mul_of_nonneg_left
    (Real.pow_mul_exp_neg_mul_sq_le_tangent (plattZetaTimeDegree k i)
      (by positivity : 0 ≤ 1 / (2 * h ^ 2)) hR (by positivity : 0 ≤ (n : ℝ) / A + R))
    (plattZetaTimeCoeff_nonneg k t₀ i)
  rw [he, add_sub_cancel_right] at ht
  rw [← sq_abs v, hv]
  simpa only [plattSincTailCoeff, mul_assoc] using ht

/-- Both tail denominators are strictly positive under the cutoff condition. -/
theorem plattSincTail_denominator_pos (k : ℕ) {h A R : ℝ} (hh : 0 < h)
    (hA : 0 < A) (hR : 0 < R) (hk : ((k : ℝ) + 1) * h ^ 2 < R ^ 2) (i : Bool) :
    0 < 1 - Real.exp (-plattSincTailRate k h R i / A) := by
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (plattSincTailRate_pos k hh hR hk i)) hA

/-- Exact geometric summation of the common tail majorant. -/
theorem hasSum_plattSincTailMajorant (k : ℕ) (t₀ : ℝ) {h A R : ℝ}
    (hh : 0 < h) (hA : 0 < A) (hR : 0 < R) (hk : ((k : ℝ) + 1) * h ^ 2 < R ^ 2) :
    HasSum (plattSincTailMajorant k t₀ h A R)
      (∑ i : Bool, plattSincTailCoeff k t₀ h R i /
        (1 - Real.exp (-plattSincTailRate k h R i / A))) := by
  change HasSum (fun n : ℕ => ∑ i : Bool, plattSincTailCoeff k t₀ h R i *
    Real.exp (-plattSincTailRate k h R i * ((n : ℝ) / A))) _
  have hi (i : Bool) :=
    (Fourier.hasSum_exp_lattice (plattSincTailRate_pos k hh hR hk i) (inv_pos.mpr hA) 0).mul_left
      (plattSincTailCoeff k t₀ h R i)
  simpa only [div_eq_mul_inv, add_zero, mul_zero, Real.exp_zero, one_mul]
    using hasSum_sum (s := Finset.univ) (fun i _ => hi i)

end

end PrimeFactorUnimodality
