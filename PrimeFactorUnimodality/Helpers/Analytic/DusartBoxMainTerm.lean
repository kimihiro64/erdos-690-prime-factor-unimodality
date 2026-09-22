import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPowerTransform

/-! # Exact linear main term of the box transform

The exponent-one case of the power identity evaluates the main term,
including the lower endpoint and the complete half-width correction.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex intervalIntegral

theorem finiteLaplace_dusartBoxWeight_neg_one (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) :
    finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-1) =
      (x : ℂ) + (m + 3 : ℕ) * (h : ℂ) / 2 - 1 := by
  have he := finiteLaplace_dusartBoxWeight_add_inv m hh hx (s := 1) one_ne_zero
  simp only [cpow_one, div_one] at he
  have hid : iteratedBoxAverageComplex h (m + 3) (fun t => (t : ℂ)) x =
      ((x + (m + 3 : ℕ) * h / 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · exact iteratedBoxAverage_id hh (m + 3) x
    · exact iteratedBoxAverage_const hh.ne' (m + 3) 0 x
  push_cast at hid
  rw [hid] at he
  push_cast
  linear_combination he

end

end PrimeFactorUnimodality
