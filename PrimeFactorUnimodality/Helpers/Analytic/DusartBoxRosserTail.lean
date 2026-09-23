import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxHighTail
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserWindow
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserSymmetry

/-! # The complete box tail controlled by Rosser's weighted integral

The full higher-order decay is summed over both ordinate signs and every
cutoff multiplicity. A positive region constant is kept arbitrary; the
initial constant `56` is supplied by the already proved actual zero-free
theorem. The remaining quantities are convergent real integrals, not zero sums.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real intervalIntegral

/-- The complete higher-order tail budget expressed through weighted real integrals. -/
def dusartBoxRosserTailBudget (m : ℕ) (h x R T : ℝ) : ℝ :=
  (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
    (2 * (xiRosserTailIntegral (Real.log x / R) (m + 4 : ℕ) T +
      2 * (Real.log T + 17) * logDampedPower (Real.log x / R) (m + 4 : ℕ) T))

/-- The actual damped tail controls the high sum without a turning-point restriction. -/
theorem norm_dusartBoxXiHighSum_le_actual_tail (m : ℕ) {h x R T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hT : 1 < T)
    (hreg : ∀ p : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue p).im| →
      (riemannXiDivisorZeroValue p).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue p).im|)) :
    ‖dusartBoxXiHighSum m h x T‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        xiRosserAbsoluteTail (Real.log x / R) (m + 4 : ℕ) T := by
  let P : RiemannXiDivisorZeroIndex → Prop :=
    fun p => T ≤ |(riemannXiDivisorZeroValue p).im|
  let C := 2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)
  have hs := ((summable_dusartBox_xi_power_average m hh hx).subtype P).norm
  have hk := (summable_xi_abs_logDampedPower
    (div_nonneg (Real.log_pos hx).le hR.le)
    (by norm_cast; omega : (2 : ℝ) ≤ (m + 4 : ℕ)) hT
    (P := P) (fun _ hp => hp)).mul_left C
  calc
    ‖dusartBoxXiHighSum m h x T‖ ≤ _ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' p : {p : RiemannXiDivisorZeroIndex // P p},
        C * logDampedPower (Real.log x / R) (m + 4 : ℕ)
          |(riemannXiDivisorZeroValue p.1).im| := by
      apply hs.tsum_le_tsum _ hk
      intro p
      exact norm_dusartBox_atom_le_abs_rosser_kernel m hh hx hR (hT.trans_le p.2)
        (riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p.1)).1
        (hreg p.1 p.2)
    _ = _ := by rw [tsum_mul_left]; rfl


/-- Any proved region supplies the complete closed high-zero norm bound. -/
theorem norm_dusartBoxXiHighSum_le_rosserTail (m : ℕ) {h x R T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hT : 10 < T)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ p : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue p).im| →
      (riemannXiDivisorZeroValue p).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue p).im|)) :
    ‖dusartBoxXiHighSum m h x T‖ ≤ dusartBoxRosserTailBudget m h x R T := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have ha : 0 ≤ Real.log x / R := div_nonneg (Real.log_pos hx).le hR.le
  have hq : (2 : ℝ) ≤ (m + 4 : ℕ) := by norm_cast; omega
  exact (norm_dusartBoxXiHighSum_le_actual_tail m hh hx hR (by linarith) hreg).trans
    (mul_le_mul_of_nonneg_left (xiRosserAbsoluteTail_le_integral ha hq hT hpeak) (by positivity))

/-- The initial region gives an unconditional full-tail estimate beyond the turning height. -/
theorem norm_dusartBoxXiHighSum_le_initialRosserTail (m : ℕ) {h x T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T)
    (hpeak : exp (sqrt ((Real.log x / 56) / (m + 4 : ℕ))) ≤ T) :
    ‖dusartBoxXiHighSum m h x T‖ ≤ dusartBoxRosserTailBudget m h x 56 T := by
  apply norm_dusartBoxXiHighSum_le_rosserTail m hh hx (by norm_num) (by linarith) hpeak
  intro p hp
  have hz := xi_zero_gap_initial (riemannXiDivisorZeroValue_eq_zero p) (hT.trans hp)
  linarith

end

end PrimeFactorUnimodality
