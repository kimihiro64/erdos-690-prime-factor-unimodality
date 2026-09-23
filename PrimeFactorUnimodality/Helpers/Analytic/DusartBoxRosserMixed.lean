import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserFixedRelative
import PrimeFactorUnimodality.Helpers.Analytic.DusartPsiRelativeAverages

/-! # Complete cutoff selection for the actual Rosser psi estimate

Use the growing cutoff when both its height and sharp-parameter conditions
hold, and the fixed-height estimate otherwise. The proved domain cover
guarantees the latter's turning-height condition. Each adjacent average
makes its own selection; no common-branch assumption restricts the range.
The low-height locations and high-region theorem remain explicit inputs.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

/-- The two scalar conditions allowing the growing sharp-tail estimate. -/
def dusartRosserGrowthDomain (m : ℕ) (x R ν H : ℝ) : Prop :=
  H ≤ exp (ν * sqrt (Real.log x / R)) ∧
    Real.log (2 * π) ≤ 1 / (m + 3 : ℕ) + sqrt ((Real.log x / R) / (m + 3 : ℕ))

/-- If the growing domain is unavailable, the fixed-height tail is admissible. -/
theorem dusartRosserGrowthDomain_or_fixed (m : ℕ) {x R ν H : ℝ}
    (hx : 1 < x) (hR : 0 < R) (hν : 0 < ν) (hH : 20 ≤ H)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2) :
    exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ H ∨
      dusartRosserGrowthDomain m x R ν H := by
  let X := sqrt (Real.log x / R)
  have hX : 0 < X := sqrt_pos.mpr (div_pos (Real.log_pos hx) hR)
  have hXsq : X ^ 2 = Real.log x / R := sq_sqrt (div_nonneg (Real.log_pos hx).le hR.le)
  have hq : ((m + 3 : ℕ) : ℝ) + 1 = (m + 4 : ℕ) := by push_cast; ring
  have he := logDampedPower_cutoff_cover (b := 2 * π) hX
    (by positivity : (0 : ℝ) < (m + 3 : ℕ)) hν (by positivity)
    (by linarith [Real.pi_lt_four] : 2 * π ≤ H) hmargin
  simpa only [hXsq, hq, dusartRosserGrowthDomain] using he

/-- The selected normalized budget; the fixed branch uses the admissible exponent `m+3`. -/
def dusartBoxRosserMixedBudget (m : ℕ) (s x R ν a H δ : ℝ) : ℝ := by
  classical
  exact if dusartRosserGrowthDomain m x R ν H then
    dusartBoxRosserRelativeBudget m s x R ν a H δ
  else dusartBoxRosserFixedRelativeBudget m s x R (m + 3 : ℕ) a H δ

/-- Selection agrees exactly with the growing budget on its domain, including the boundary. -/
theorem dusartBoxRosserMixedBudget_of_growth (m : ℕ) (s x R ν a H δ : ℝ)
    (hg : dusartRosserGrowthDomain m x R ν H) :
    dusartBoxRosserMixedBudget m s x R ν a H δ =
      dusartBoxRosserRelativeBudget m s x R ν a H δ := by
  simp only [dusartBoxRosserMixedBudget, ite_eq_left hg]

/-- Outside the growing domain, selection agrees exactly with the fixed-height budget. -/
theorem dusartBoxRosserMixedBudget_of_fixed (m : ℕ) (s x R ν a H δ : ℝ)
    (hg : ¬ dusartRosserGrowthDomain m x R ν H) :
    dusartBoxRosserMixedBudget m s x R ν a H δ =
      dusartBoxRosserFixedRelativeBudget m s x R (m + 3 : ℕ) a H δ := by
  simp only [dusartBoxRosserMixedBudget, ite_eq_right hg]

/-- The actual average has a selected estimate at every base point above one. -/
theorem abs_dusartPsiAverageError_div_le_rosserMixed (m : ℕ) {s x R ν a H δ : ℝ}
    (hs : 0 < s) (hx : 1 < x) (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxRosserMixedBudget m s x R ν a H δ := by
  by_cases hg : dusartRosserGrowthDomain m x R ν H
  · rw [dusartBoxRosserMixedBudget_of_growth _ _ _ _ _ _ _ _ hg]
    exact abs_dusartPsiAverageError_div_le_rosserRelative m hs hx hR hν hν1 hmargin hg.2
      ha haH (by linarith) hδ hg.1 hgap hreg
  · rw [dusartBoxRosserMixedBudget_of_fixed _ _ _ _ _ _ _ _ hg]
    have hpeak :=
      (dusartRosserGrowthDomain_or_fixed m hx hR hν (by linarith) hmargin).resolve_right hg
    exact abs_dusartPsiAverageError_div_le_rosserFixed m hs hx hR
      (by norm_cast; omega) (by norm_cast; omega) ha haH hH hδ hgap hpeak hreg

/-- Pointwise control allows the left and right averages to select different cutoff branches. -/
theorem abs_psi_sub_div_le_dusartBoxRosserMixed (m : ℕ) {s x R ν a H δ : ℝ}
    (hs : 0 < s) (hx : 0 < x) (hl : 1 < x * (1 - (m + 3 : ℕ) * s))
    (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1) (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤
      max ((1 - (m + 3 : ℕ) * s) *
        dusartBoxRosserMixedBudget m (s / (1 - (m + 3 : ℕ) * s))
          (x * (1 - (m + 3 : ℕ) * s)) R ν a H δ)
        (dusartBoxRosserMixedBudget m s x R ν a H δ) + (m + 3 : ℕ) * s / 2 := by
  have hy0 : 0 < x * (1 - (m + 3 : ℕ) * s) := lt_trans zero_lt_one hl
  have ht : 0 < 1 - (m + 3 : ℕ) * s := (mul_pos_iff_of_pos_left hx).mp hy0
  have hsx : 0 ≤ (m + 3 : ℕ) * s * x := by positivity
  have hx1 : 1 < x := by nlinarith only [hl, hsx]
  have hstep : (s / (1 - (m + 3 : ℕ) * s)) * (x * (1 - (m + 3 : ℕ) * s)) = s * x := by
    calc
      _ = (s * x) * ((1 - (m + 3 : ℕ) * s) / (1 - (m + 3 : ℕ) * s)) := by ring
      _ = _ := by rw [div_self ht.ne', mul_one]
  have hlo := abs_dusartPsiAverageError_div_le_rosserMixed m (div_pos hs ht) hl
    hR hν hν1 hmargin ha haH hH hδ hgap hreg
  rw [hstep] at hlo
  exact dusart_abs_psi_div_le_of_relative_averages (m + 3) hs hx hy0 hlo
    (abs_dusartPsiAverageError_div_le_rosserMixed m hs hx1 hR hν hν1 hmargin
      ha haH hH hδ hgap hreg)

end

end PrimeFactorUnimodality
