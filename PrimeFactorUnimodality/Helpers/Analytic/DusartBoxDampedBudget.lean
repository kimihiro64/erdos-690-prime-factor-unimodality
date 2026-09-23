import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxDampedTailBound
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxTwoCutoffBudget

/-! # A fully explicit damped-tail budget for the actual pointwise psi error

An auxiliary cutoff evaluates the damped infinite tail using two proved
Lehman bounds. Taking the minimum with the previous bound preserves the
better estimate at every evaluation point. Only a fixed low-height gap
and admissible scalar parameters remain inputs to the provider theorem.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev

/-- Choose the better of the original high bound and the damped split bound. -/
def dusartBoxDampedTailBudget (x T B : ℝ) : ℝ :=
  min (4 * xiLehmanHighBound (T / 2) (T / 2))
    (Real.exp (-(1 / (56 * Real.log B)) * Real.log x) *
      (4 * xiLehmanHighBound (T / 2) (T / 2)) + 4 * xiLehmanHighBound (B / 2) (B / 2))

/-- The actual high sum satisfies either estimate, hence their minimum. -/
theorem norm_dusartBoxXiHighSum_le_dampedBudget (m : ℕ) {h x T B : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T) (hTB : T ≤ B) :
    ‖dusartBoxXiHighSum m h x T‖ ≤ dusartBoxTailFactor m h x T *
      dusartBoxDampedTailBudget x T B := by
  unfold dusartBoxDampedTailBudget
  by_cases he : 4 * xiLehmanHighBound (T / 2) (T / 2) ≤
      Real.exp (-(1 / (56 * Real.log B)) * Real.log x) *
        (4 * xiLehmanHighBound (T / 2) (T / 2)) + 4 * xiLehmanHighBound (B / 2) (B / 2)
  · rw [min_eq_left he]
    exact norm_dusartBoxXiHighSum_le_highBound m hh hx hT
  · rw [min_eq_right (le_of_not_ge he)]
    exact norm_dusartBoxXiHighSum_le_split_highBound m hh hx hT hTB

/-- Complete finite-zero, infinite-zero, negative-even, and endpoint contributions. -/
def dusartBoxDampedErrorBudget (m : ℕ) (h x a H T B δ : ℝ) : ℝ :=
  dusartBoxLowBandBudget m h x a H T δ +
    dusartBoxTailFactor m h x T * dusartBoxDampedTailBudget x T B +
    1 / (2 * (x ^ 2 - 1)) + Real.log (2 * Real.pi)

/-- Retaining damping can never make the previous explicit scalar estimate worse. -/
theorem dusartBoxDampedErrorBudget_le_twoCutoff (m : ℕ) {h x a H T B δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 0 < T) :
    dusartBoxDampedErrorBudget m h x a H T B δ ≤
      dusartBoxTwoCutoffErrorBudget m h x a H T δ := by
  have ht := mul_le_mul_of_nonneg_left
    (min_le_left (4 * xiLehmanHighBound (T / 2) (T / 2))
      (Real.exp (-(1 / (56 * Real.log B)) * Real.log x) *
        (4 * xiLehmanHighBound (T / 2) (T / 2)) + 4 * xiLehmanHighBound (B / 2) (B / 2)))
    (dusartBoxTailFactor_nonneg m hh hx hT)
  exact add_le_add (add_le_add (add_le_add le_rfl ht) le_rfl) le_rfl

/-- The actual averaged psi error satisfies the fully explicit damped budget. -/
theorem abs_dusartPsiAverageError_le_dampedBudget (m : ℕ) {h x a H T B δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hTB : T ≤ B) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxDampedErrorBudget m h x a H T B δ := by
  have hz := norm_add_le
    ((∑ p ∈ xiLowHeightIndices H, intervalIntegral.iteratedBoxAverageComplex h (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x) +
      ∑ p ∈ xiHeightBandIndices H T, intervalIntegral.iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x)
    (dusartBoxXiHighSum m h x T)
  have he := hz.trans (add_le_add
    (norm_dusartBox_low_add_band_le m hh hx ha haH hH hHT hδ hgap)
    (norm_dusartBoxXiHighSum_le_dampedBudget m hh hx (hH.trans hHT) hTB))
  rw [← smoothedXiPairedSum_box_eq_low_add_band_add_high m hh hx hHT] at he
  exact (abs_dusartPsiAverageError_le_zero_sum m hh hx).trans
    (add_le_add (add_le_add he le_rfl) le_rfl)

/-- Both adjacent averages bound the pointwise error, with its exact smoothing loss. -/
theorem abs_psi_sub_le_dusartBoxDampedBudget (m : ℕ) {h x a H T B δ : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hTB : T ≤ B) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    |ψ x - x| ≤
      max (dusartBoxDampedErrorBudget m h (x - (m + 3 : ℕ) * h) a H T B δ)
        (dusartBoxDampedErrorBudget m h x a H T B δ) + (m + 3 : ℕ) * h / 2 := by
  have hx' : 1 < x := by
    have hn : 0 ≤ (m + 3 : ℕ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
    linarith
  exact dusart_abs_psi_error_le_of_averages (m + 3) hh
    ((abs_dusartPsiAverageError_le_dampedBudget m hh hx ha haH hH hHT hTB hδ hgap).trans
      (le_max_left _ _))
    ((abs_dusartPsiAverageError_le_dampedBudget m hh hx' ha haH hH hHT hTB hδ hgap).trans
      (le_max_right _ _))

/-- The scalar obligation has no unevaluated zero sums or zero-location predicates. -/
def HasDusartDampedScalarBudget (A X H δ : ℝ) : Prop :=
  ∀ x : ℝ, X ≤ x → ∃ (m : ℕ) (h a T B : ℝ),
    0 < h ∧ 1 < x - (m + 3 : ℕ) * h ∧ 10 ≤ a ∧ a < H ∧ H ≤ T ∧ T ≤ B ∧
      max (dusartBoxDampedErrorBudget m h (x - (m + 3 : ℕ) * h) a H T B δ)
        (dusartBoxDampedErrorBudget m h x a H T B δ) + (m + 3 : ℕ) * h / 2 ≤
          A * x / (Real.log x) ^ 4

/-- The proved explicit estimates leave only a fixed low input and real scalar inequalities. -/
theorem hasPsiLogFourthError_of_dampedBudget {A X H δ : ℝ}
    (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (h : HasDusartDampedScalarBudget A X H δ) : HasPsiLogFourthError A X := by
  intro x hx
  obtain ⟨m, step, a, T, B, hs, hl, ha, haH, hHT, hTB, hb⟩ := h x hx
  exact (abs_psi_sub_le_dusartBoxDampedBudget m hs hl ha haH hH hHT hTB hδ hgap).trans hb

/-- The exact fixed-cutoff theta coefficient follows from the damped scalar proof. -/
theorem hasThetaLogFourthError_648_of_dampedBudget {H δ : ℝ}
    (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (h : HasDusartDampedScalarBudget (1 / 2) (4e18) H δ) :
    HasThetaLogFourthError (648 / 1000) (4e18) := by
  convert hasThetaLogFourthError_of_psiLogFourthError_sharp le_rfl
    (hasPsiLogFourthError_of_dampedBudget hH hδ hgap h) using 1
  norm_num

end

end PrimeFactorUnimodality
