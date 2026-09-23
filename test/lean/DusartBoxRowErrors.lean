import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRowErrors

/-! # Rational row radii and an actual psi consumer without unknown-ordinate hypotheses -/

open PrimeFactorUnimodality Complex Finset

example : (XiSignRow.mk 14 15).center = 29 / 2 := by norm_num [XiSignRow.center]

example : (XiSignRow.mk 14 15).radius = 1 / 2 := by norm_num [XiSignRow.radius]

example {γ : ℝ} (hγ : γ ∈ Set.Icc 14 15) : |γ - 29 / 2| ≤ 1 / 2 := by
  have h := (XiSignRow.mk 14 15).abs_sub_center_le hγ
  norm_num [XiSignRow.center, XiSignRow.radius] at h ⊢
  exact h

example (m : ℕ) (s u V : ℝ) (c : Fin 0 → ℂ) (e : Fin 0 → ℝ) :
    dusartBoxRowsError Fin.elim0 m s u V c e = 0 := by simp [dusartBoxRowsError]

example {n k : ℕ} {rows : Fin n → XiSignRow} {padding : Fin k → XiSignRow} {a b : ℚ}
    (h : XiSignRows.Valid rows 0 a) (hp : XiSignRows.Valid padding a b) (ha : 32 ≤ a)
    (hm : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b <
        (b : ℝ) - a + (XiSignRows.completedAreaRat (Fin.append rows padding) a b : ℝ))
    (m : ℕ) {s x : ℝ} (u : ℝ) (hs : 0 < s) (hx : 1 < x) {V : ℝ}
    (hv : |Real.log x - u| ≤ V) (hl : ∀ i, 0 < (rows i).lower)
    (c : Fin n → ℂ) (e : Fin n → ℝ)
    (hc : ∀ i, ‖dusartBoxOrdinateCoefficient m s u (rows i).center - c i‖ ≤ e i)
    {z : ℂ} {ε : ℝ}
    (hz : ‖(∑ i, c i * exp (I * ↑((Real.log x - u) * (rows i).center))) - z‖ ≤ ε) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxPhaseBudget m s x a (2 * |z.re| + 2 * (dusartBoxRowsError rows m s u V c e + ε)) :=
  h.abs_psi_average_le_of_center_enclosures hp ha hm m u hs hx hv hl c e hc hz
