import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserMixed

/-! # All-range cutoff selection with the explicit log-fourth step

The fixed and growing estimates are selected independently at the two
adjacent base points. Their domain conditions are proved by the cutoff
cover, not left as restrictions on the starting range. The remaining
inputs are the actual low-zero gap, high region, and uniform scalar bound.
These are not asserted by the psi and theta transfer theorems below.
The fourth-power coefficient is an optional sufficient route, not the
theta statement requested by Wang--Crapis; use the direct theta transfer
when proving those published margins.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

/-- The selected two-average contribution, with the smoothing step fixed explicitly. -/
def dusartLogFourthMixedBoxBound (m : ℕ) (x R ν a H δ : ℝ) : ℝ :=
  let s := dusartLogFourthRelativeStep m x
  let t := 1 - 1 / (4 * Real.log x ^ 4)
  max (t * dusartBoxRosserMixedBudget m (s / t) (dusartLogFourthLeft x) R ν a H δ)
    (dusartBoxRosserMixedBudget m s x R ν a H δ)

/-- Every base point above three has the selected actual bound and exact smoothing allowance. -/
theorem abs_psi_sub_div_le_logFourthMixedBox (m : ℕ) {x R ν a H δ : ℝ}
    (hx : 3 ≤ x) (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤ dusartLogFourthMixedBoxBound m x R ν a H δ + 1 / (8 * Real.log x ^ 4) := by
  have hx1 : 1 < x := by linarith
  have hleft : x * (1 - (m + 3 : ℕ) * dusartLogFourthRelativeStep m x) =
      dusartLogFourthLeft x := by rw [dusartLogFourthRelativeStep_width m hx1]; rfl
  have hb := abs_psi_sub_div_le_dusartBoxRosserMixed m
    (dusartLogFourthRelativeStep_pos m hx1) (by linarith : 0 < x)
    (by rw [hleft]; exact one_lt_dusartLogFourthLeft hx) hR hν hν1 hmargin
    ha haH hH hδ hgap hreg
  rw [dusartLogFourthRelativeStep_loss m hx1, dusartLogFourthRelativeStep_width m hx1] at hb
  exact hb

/-- The selected scalar allowance gives the half-sized fourth-power psi coefficient. -/
theorem abs_psi_sub_le_half_logFourth_of_mixed (m : ℕ) {x R ν a H δ : ℝ}
    (hx : 3 ≤ x) (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|))
    (hbound : dusartLogFourthMixedBoxBound m x R ν a H δ ≤ 3 / (8 * Real.log x ^ 4)) :
    |ψ x - x| ≤ (1 / 2) * x / Real.log x ^ 4 := by
  have hb := (abs_psi_sub_div_le_logFourthMixedBox m hx hR hν hν1 hmargin
    ha haH hH hδ hgap hreg).trans (add_le_add hbound le_rfl)
  have hx0 : 0 < x := by linarith
  have he : 3 / (8 * Real.log x ^ 4) + 1 / (8 * Real.log x ^ 4) =
      ((1 / 2) * x / Real.log x ^ 4) / x := by
    field_simp
    ring
  rw [he] at hb
  exact (div_le_div_iff_of_pos_right hx0).mp hb

/-- A uniform selected scalar estimate supplies the actual psi provider on the full stated ray. -/
theorem hasPsiLogFourthError_of_rosserMixed {X R a H δ : ℝ}
    (hX : 3 ≤ X) (hR : 0 < R) (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|))
    (hscalar : ∀ x : ℝ, X ≤ x → ∃ (m : ℕ) (ν : ℝ),
      0 < ν ∧ ν ≤ 1 ∧ 1 < (m + 3 : ℕ) * ν ^ 2 ∧
        dusartLogFourthMixedBoxBound m x R ν a H δ ≤ 3 / (8 * Real.log x ^ 4)) :
    HasPsiLogFourthError (1 / 2) X := by
  intro x hx
  obtain ⟨m, ν, hν, hν1, hm, hb⟩ := hscalar x hx
  exact abs_psi_sub_le_half_logFourth_of_mixed m (hX.trans hx) hR hν hν1 hm
    ha haH hH hδ hgap hreg hb

/-- The same inputs supply the optional fourth-power theta estimate. -/
theorem hasThetaLogFourthError_648_of_rosserMixed {R a H δ : ℝ}
    (hR : 0 < R) (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|))
    (hscalar : ∀ x : ℝ, (4e18 : ℝ) ≤ x → ∃ (m : ℕ) (ν : ℝ),
      0 < ν ∧ ν ≤ 1 ∧ 1 < (m + 3 : ℕ) * ν ^ 2 ∧
        dusartLogFourthMixedBoxBound m x R ν a H δ ≤ 3 / (8 * Real.log x ^ 4)) :
    HasThetaLogFourthError (648 / 1000) (4e18) := by
  convert hasThetaLogFourthError_of_psiLogFourthError_sharp le_rfl
    (hasPsiLogFourthError_of_rosserMixed (by norm_num) hR ha haH hH hδ hgap hreg hscalar) using 1
  norm_num

end

end PrimeFactorUnimodality
