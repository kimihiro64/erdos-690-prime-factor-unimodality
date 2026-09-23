import PrimeFactorUnimodality.Helpers.Analytic.TuringXiLogBudget
import PrimeFactorUnimodality.Helpers.Analytic.TuringXiLogInterchange
import PrimeFactorUnimodality.Helpers.Analytic.XiLogRatio

/-! # The actual integrated xi log ratio and its explicit bound

Horizontal xi zeros form a null set, even at a height containing zeros.
The endpoint log-ratio formula and absolute interchange therefore identify
the actual integral with the complete spectral budget, without a zero-free
horizontal-segment assumption.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory

/-- On every horizontal line, xi is nonzero almost everywhere in the real coordinate. -/
theorem ae_riemannXi_horizontal_ne_zero (a T : ℝ) :
    ∀ᵐ x : ℝ, riemannXi ((x : ℂ) + (a : ℂ) + T * I) ≠ 0 := by
  have he : ∀ᵐ x : ℝ, ∀ p : RiemannXiDivisorZeroIndex,
      x ≠ (riemannXiDivisorZeroValue p).re - a :=
    ae_all_iff.mpr (fun p => volume.ae_ne _)
  filter_upwards [he] with x hx
  intro hz
  obtain ⟨p, hp⟩ := exists_xi_divisor_index_of_zero hz
  have hr := congrArg Complex.re hp
  simp only [add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im,
    mul_zero, zero_mul, sub_self, add_zero] at hr
  exact hx p (by linarith)

/-- The actual xi log-modulus increment along the shifted unit interval. -/
def turingXiLogIncrement (T x : ℝ) : ℝ :=
  Real.log ‖riemannXi ((x : ℂ) + ((1 / 2 : ℂ) + T * I) + 1)‖ -
    Real.log ‖riemannXi ((x : ℂ) + ((1 / 2 : ℂ) + T * I))‖

/-- The pointwise distance series identifies the actual increment outside a null set. -/
theorem ae_turingXiLogIncrement_eq_tsum (T : ℝ) :
    turingXiLogIncrement T =ᵐ[volume] (fun x => ∑' p, turingXiLogAtom T p x) := by
  filter_upwards [ae_riemannXi_horizontal_ne_zero (1 / 2) T,
    ae_riemannXi_horizontal_ne_zero (3 / 2) T] with x hx hx1
  have h0 : riemannXi ((x : ℂ) + ((1 / 2 : ℂ) + T * I)) ≠ 0 := by
    simpa only [ofReal_div, ofReal_one, ofReal_ofNat, add_assoc] using hx
  have h1 : riemannXi ((x : ℂ) + ((1 / 2 : ℂ) + T * I) + 1) ≠ 0 := by
    convert hx1 using 1
    push_cast
    congr 1
    ring
  rw [turingXiLogIncrement, log_norm_riemannXi_step_eq_tsum h0 h1]
  apply tsum_congr
  intro p
  unfold turingXiLogAtom logNormStep
  have ha : (x : ℂ) + ((1 / 2 : ℂ) + T * I) + 1 - riemannXiDivisorZeroValue p =
      ((x + 1 : ℝ) : ℂ) - (riemannXiDivisorZeroValue p - ((1 / 2 : ℂ) + T * I)) := by
    push_cast
    ring
  have hb : (x : ℂ) + ((1 / 2 : ℂ) + T * I) - riemannXiDivisorZeroValue p =
      (x : ℂ) - (riemannXiDivisorZeroValue p - ((1 / 2 : ℂ) + T * I)) := by ring
  rw [ha, hb]

/-- The actual xi logarithmic increment is integrable, including zero-containing heights. -/
theorem intervalIntegrable_turingXiLogIncrement (T : ℝ) :
    IntervalIntegrable (turingXiLogIncrement T) volume 0 1 :=
  (intervalIntegrable_tsum_turingXiLogAtom T).congr_ae
    (ae_restrict_of_ae (ae_turingXiLogIncrement_eq_tsum T).symm)

/-- Exact identification of the actual integrated xi ratio with the complete divisor budget. -/
theorem integral_turingXiLogIncrement_eq_tsum (T : ℝ) :
    (∫ x in (0 : ℝ)..1, turingXiLogIncrement T x) = ∑' p, turingXiLogStep T p := by
  calc
    _ = ∫ x in (0 : ℝ)..1, ∑' p, turingXiLogAtom T p x :=
      intervalIntegral.integral_congr_ae
        ((ae_turingXiLogIncrement_eq_tsum T).mono (fun _ hx _ => hx))
    _ = _ := integral_tsum_turingXiLogAtom T

/-- The actual integrated xi ratio satisfies the explicit logarithmic spectral bound. -/
theorem integral_turingXiLogIncrement_le (T : ℝ) :
    (∫ x in (0 : ℝ)..1, turingXiLogIncrement T x) ≤
      8 * Real.log (|T| / 2 + 3) + 88 := by
  rw [integral_turingXiLogIncrement_eq_tsum]
  exact tsum_turingXiLogStep_le_explicit T

end

end PrimeFactorUnimodality
