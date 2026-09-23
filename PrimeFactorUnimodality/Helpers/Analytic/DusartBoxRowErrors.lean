import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxCoefficientStability
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.ExponentialStability

/-! # Midpoint data control every ordinate in the complete zero rows

One coefficient enclosure at each rational midpoint is shared by every
sample. Analytic stability accounts for the unknown zero position, and the
phase bound accounts separately for ordinate rounding over the whole window.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Finset

/-- Rational midpoint of the stored zero enclosure. -/
def XiSignRow.center (row : XiSignRow) : ℚ := (row.lower + row.upper) / 2

/-- Rational half-width of the stored zero enclosure. -/
def XiSignRow.radius (row : XiSignRow) : ℚ := (row.upper - row.lower) / 2

/-- Every enclosed ordinate lies within the midpoint radius, including the endpoints. -/
theorem XiSignRow.abs_sub_center_le {row : XiSignRow} {γ : ℝ}
    (hγ : γ ∈ Set.Icc (row.lower : ℝ) row.upper) :
    |γ - (row.center : ℝ)| ≤ row.radius := by
  unfold XiSignRow.center XiSignRow.radius
  push_cast
  exact abs_le.mpr ⟨by linarith [hγ.1], by linarith [hγ.2]⟩

/-- A center coefficient enclosure extends to the entire closed zero interval. -/
theorem XiSignRow.norm_coefficient_sub_le (row : XiSignRow) (m : ℕ) {s : ℝ}
    (hs : 0 < s) (u : ℝ) (hl : 0 < row.lower) {γ : ℝ}
    (hγ : γ ∈ Set.Icc (row.lower : ℝ) row.upper) {c : ℂ} {e : ℝ}
    (hc : ‖dusartBoxOrdinateCoefficient m s u row.center - c‖ ≤ e) :
    ‖dusartBoxOrdinateCoefficient m s u γ - c‖ ≤
      dusartBoxCoefficientSlope m s u row.lower * row.radius + e := by
  have hL : (0 : ℝ) < row.lower := by exact_mod_cast hl
  have hcenter : (row.lower : ℝ) ≤ row.center := by
    unfold XiSignRow.center
    push_cast
    linarith [hγ.1, hγ.2]
  exact norm_dusartBoxOrdinateCoefficient_sub_center_le m hs u hL hγ.1 hcenter
    (row.abs_sub_center_le hγ) hc

/-- Total coefficient and phase rounding cost, shared across a whole logarithmic window. -/
def dusartBoxRowsError {n : ℕ} (rows : Fin n → XiSignRow) (m : ℕ) (s u V : ℝ)
    (c : Fin n → ℂ) (e : Fin n → ℝ) : ℝ :=
  ∑ i, (dusartBoxCoefficientSlope m s u (rows i).lower * (rows i).radius + e i +
    ‖c i‖ * (V * (rows i).radius))

/-- Finite midpoint checks replace a universal unknown-ordinate enclosure premise. -/
theorem norm_dusartBoxRowSum_sub_centers_le {n : ℕ} (rows : Fin n → XiSignRow)
    (m : ℕ) {s : ℝ} (hs : 0 < s) (u : ℝ) {v V : ℝ} (hv : |v| ≤ V)
    (hl : ∀ i, 0 < (rows i).lower) (c : Fin n → ℂ) (e : Fin n → ℝ)
    (hc : ∀ i, ‖dusartBoxOrdinateCoefficient m s u (rows i).center - c i‖ ≤ e i)
    (γ : Fin n → ℝ) (hγ : ∀ i, γ i ∈ Set.Icc ((rows i).lower : ℝ) (rows i).upper) :
    ‖(∑ i, dusartBoxOrdinateCoefficient m s u (γ i) * exp (I * ↑(v * γ i))) -
      ∑ i, c i * exp (I * ↑(v * (rows i).center))‖ ≤ dusartBoxRowsError rows m s u V c e :=
  norm_expSum_sub_expSum_le_of_enclosures univ _ c γ (fun i => (rows i).center)
    (fun i => dusartBoxCoefficientSlope m s u (rows i).lower * (rows i).radius + e i)
    (fun i => (rows i).radius) hv
    (fun i _ => (rows i).norm_coefficient_sub_le m hs u (hl i) (hγ i) (hc i))
    (fun i _ => (rows i).abs_sub_center_le (hγ i))

/-- An approximation of the midpoint phase sum includes all row-position and sample errors. -/
theorem norm_dusartBoxRowSum_sub_sample_le {n : ℕ} (rows : Fin n → XiSignRow)
    (m : ℕ) {s : ℝ} (hs : 0 < s) (u : ℝ) {v V : ℝ} (hv : |v| ≤ V)
    (hl : ∀ i, 0 < (rows i).lower) (c : Fin n → ℂ) (e : Fin n → ℝ)
    (hc : ∀ i, ‖dusartBoxOrdinateCoefficient m s u (rows i).center - c i‖ ≤ e i)
    {z : ℂ} {ε : ℝ} (hz : ‖(∑ i, c i * exp (I * ↑(v * (rows i).center))) - z‖ ≤ ε)
    (γ : Fin n → ℝ) (hγ : ∀ i, γ i ∈ Set.Icc ((rows i).lower : ℝ) (rows i).upper) :
    ‖(∑ i, dusartBoxOrdinateCoefficient m s u (γ i) * exp (I * ↑(v * γ i))) - z‖ ≤
      dusartBoxRowsError rows m s u V c e + ε :=
  (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (norm_dusartBoxRowSum_sub_centers_le rows m hs u hv hl c e hc γ hγ) hz)

/-- Turing-complete midpoint data feed the full actual psi-average budget. -/
theorem XiSignRows.Valid.abs_psi_average_le_of_center_enclosures {n k : ℕ}
    {rows : Fin n → XiSignRow} {padding : Fin k → XiSignRow} {a b : ℚ}
    (h : XiSignRows.Valid rows 0 a) (hpad : XiSignRows.Valid padding a b) (ha : 32 ≤ a)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b <
        (b : ℝ) - a + (XiSignRows.completedAreaRat (Fin.append rows padding) a b : ℝ))
    (m : ℕ) {s x : ℝ} (u : ℝ) (hs : 0 < s) (hx : 1 < x) {V : ℝ}
    (hv : |Real.log x - u| ≤ V) (hl : ∀ i, 0 < (rows i).lower)
    (c : Fin n → ℂ) (e : Fin n → ℝ)
    (hc : ∀ i, ‖dusartBoxOrdinateCoefficient m s u (rows i).center - c i‖ ≤ e i)
    {z : ℂ} {ε : ℝ}
    (hz : ‖(∑ i, c i * exp (I * ↑((Real.log x - u) * (rows i).center))) - z‖ ≤ ε) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxPhaseBudget m s x a (2 * |z.re| + 2 * (dusartBoxRowsError rows m s u V c e + ε)) := by
  apply h.abs_psi_average_le_of_turing_phase_enclosure hpad ha hmargin m u hs hx
  intro γ hγ
  exact norm_dusartBoxRowSum_sub_sample_le rows m hs u hv hl c e hc hz γ
    (fun i => ⟨(hγ i).1.le, (hγ i).2.le⟩)

end

end PrimeFactorUnimodality
