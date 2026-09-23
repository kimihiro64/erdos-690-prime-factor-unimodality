import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserTail
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserClosedBounds

/-! # An elementary full high-zero budget with a free power parameter

The exact real power integrals remove the improper integrals from the
Rosser budget. The actual complete spectral sum remains the consumer,
with both signs and cutoff multiplicities already accounted for.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The complete high-zero budget contains only elementary real operations. -/
def dusartBoxRosserClosedTailBudget (m : ℕ) (h x R p T : ℝ) : ℝ :=
  (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
    xiRosserClosedTailBound (Real.log x / R) (m + 4 : ℕ) p T

/-- The elementary expression majorizes the already proved integral budget. -/
theorem dusartBoxRosserTailBudget_le_closed (m : ℕ) {h x R p T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hp : 1 < p)
    (hpq : p < (m + 4 : ℕ)) (hT : 10 < T) :
    dusartBoxRosserTailBudget m h x R T ≤ dusartBoxRosserClosedTailBudget m h x R p T := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  unfold dusartBoxRosserTailBudget dusartBoxRosserClosedTailBudget xiRosserClosedTailBound
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  exact add_le_add
    (xiRosserTailIntegral_le_closed (div_nonneg (Real.log_pos hx).le hR.le)
      (by norm_cast; omega) hp hpq hT) le_rfl

/-- The actual complete high-zero sum satisfies the elementary budget. -/
theorem norm_dusartBoxXiHighSum_le_rosserClosedTail (m : ℕ) {h x R p T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hp : 1 < p)
    (hpq : p < (m + 4 : ℕ)) (hT : 10 < T)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    ‖dusartBoxXiHighSum m h x T‖ ≤ dusartBoxRosserClosedTailBudget m h x R p T :=
  (norm_dusartBoxXiHighSum_le_rosserTail m hh hx hR hT hpeak hreg).trans
    (dusartBoxRosserTailBudget_le_closed m hh hx hR hp hpq hT)

/-- The proved initial region supplies the same elementary tail without a region premise. -/
theorem norm_dusartBoxXiHighSum_le_initialRosserClosedTail (m : ℕ) {h x p T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (hT : 10 ^ 9 ≤ T) (hpeak : exp (sqrt ((Real.log x / 56) / (m + 4 : ℕ))) ≤ T) :
    ‖dusartBoxXiHighSum m h x T‖ ≤ dusartBoxRosserClosedTailBudget m h x 56 p T :=
  (norm_dusartBoxXiHighSum_le_initialRosserTail m hh hx hT hpeak).trans
    (dusartBoxRosserTailBudget_le_closed m hh hx (by norm_num) hp hpq (by linarith))

end

end PrimeFactorUnimodality
